use bitcode::__private::{Buffer, Decoder, Encoder, View};
use bitcode::{Decode, Encode};
use serde::de::{SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::Bound;
use std::fmt;
use std::num::NonZeroUsize;
use std::ops::RangeBounds;

use crate::collab::codec::{decode_entries, encode_entries, CodecError, FORMAT_VERSION};
pub use crate::collab::fractional_key::{
    FractionalKey, KeyBuf, INLINE_CAP, MAX_KEY_LEN, SESSION_SUFFIX_LEN,
};
use crate::collab::hlc::Hlc;

/// Session suffix reserved for [`virtual_key`]. No replica may use it — see
/// [`CollaborativeWorkbook::new`](crate::collab::CollaborativeWorkbook::new).
pub const VIRTUAL_SESSION: [u8; SESSION_SUFFIX_LEN] = [0; SESSION_SUFFIX_LEN];

/// The key of the `ordinal`-th (1-based) row or column that nobody ever explicitly inserted.
///
/// It is session-free and deterministic, so two replicas materializing "row 5" independently mint the
/// same key and their edits meet in the same cell. Positions are spaced two apart so that a key can
/// always be minted between two consecutive virtual ones.
#[allow(clippy::expect_used)]
pub fn virtual_key(ordinal: u32) -> FractionalKey {
    let position = (2 * ordinal).to_be_bytes();
    let mut buf = KeyBuf::from(&position[1..]);
    buf.extend_from_slice(&VIRTUAL_SESSION);
    FractionalKey::try_from_bytes(&buf).expect("virtual key is 7 bytes")
}

/// Inverse of [`virtual_key`]: `None` for anything a session actually minted.
pub fn virtual_ordinal(key: &FractionalKey) -> Option<u32> {
    let (position, session) = key.split();
    if session != VIRTUAL_SESSION || position.len() != 3 {
        return None;
    }
    let n = u32::from_be_bytes([0, position[0], position[1], position[2]]);
    if n == 0 || !n.is_multiple_of(2) {
        return None;
    }
    Some(n / 2)
}

/// A single element of a [FractionalIndex]: where it sits, and the key it answers to.
///
/// The two are the same key until the element is moved. A move mints a fresh key for the new
/// position and keeps the original as the element's [identity](Entry::identity), so peers that only
/// know the element by the key it was minted as can still find it.
#[derive(Debug, Clone, Eq, Serialize, Deserialize)]
pub struct Entry {
    pub key: FractionalKey,
    /// - On an identity record: the destination it sits on ([FractionalKey::NULL] for its own key).
    /// - On a destination record: the identity.
    pub moved: FractionalKey,
    /// Newest insert or move: the position register's stamp.
    pub moved_at: Hlc,
    /// Newest removal, kept after a revive. Zero when never removed.
    pub removed_at: Hlc,
    /// Newest cell edit under the element. Not encoded; rebuilt from the cell registers.
    pub touched_at: Hlc,
}

impl PartialEq for Entry {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
            && self.moved == other.moved
            && self.moved_at == other.moved_at
            && self.removed_at == other.removed_at
    }
}

impl Entry {
    pub fn new(key: FractionalKey, moved_at: Hlc, moved: FractionalKey) -> Self {
        Entry {
            key,
            moved,
            moved_at,
            removed_at: Hlc::new(0),
            touched_at: Hlc::new(0),
        }
    }

    pub fn moved(&self) -> Option<&FractionalKey> {
        if self.moved.is_empty() {
            None
        } else {
            Some(&self.moved)
        }
    }

    /// The identity of the element a position record (or a destination record) belongs to.
    pub fn identity(&self) -> &FractionalKey {
        self.moved().unwrap_or(&self.key)
    }

    /// On an identity record: the newest removal is at least as new as the newest insert or move.
    pub fn is_removed(&self) -> bool {
        self.removed_at >= self.moved_at
    }

    /// On an identity record: something newer than the newest removal keeps the element in place.
    pub fn is_visible(&self) -> bool {
        self.moved_at.max(self.touched_at) > self.removed_at
    }

    /// Writes `{at → moved}` into the position register if `(at, moved)` outranks
    /// `(moved_at, moved)`. Returns whether it did.
    pub fn write_position(&mut self, at: Hlc, moved: &FractionalKey) -> bool {
        if (at, moved) <= (self.moved_at, &self.moved) {
            return false;
        }
        self.moved_at = at;
        self.moved = moved.clone();
        true
    }
}

/// Where a record is filed: an index into `active` or into `moved`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Slot {
    Active(usize),
    Moved(usize),
}

/// A collection of [FractionalKey]s that enables producing them in a way that matches their desired
/// order.
#[derive(Debug, Clone, Default)]
pub struct FractionalIndex {
    /// The position record of every visible element, sorted by key.
    active: Vec<Entry>,
    /// Every other record, sorted by key.
    moved: Vec<Entry>,

    /// Suffix this replica mints new keys with. Never serialized — see [Self::decode].
    pub suffix: [u8; Self::SESSION_HASH_SIZE],

    /// Highest ordinal any [virtual_key] in this index has ever carried, cached rather than stored:
    /// it is exactly `max(virtual_ordinal(k))` over `active ∪ moved`, and it is derivable only
    /// because records are never dropped, so a key that was ever here is still in one of the two
    /// spaces. Nothing serializes it — every constructor recomputes it.
    watermark: u32,
}

/// Equality is over document state (`active`, `moved`). `suffix` is replica identity —
/// deliberately never serialized — and `watermark` is derived from the two spaces, so two
/// replicas holding the same document compare equal whatever session they mint with.
impl PartialEq for FractionalIndex {
    fn eq(&self, other: &Self) -> bool {
        self.active == other.active && self.moved == other.moved
    }
}
impl Eq for FractionalIndex {}

impl FractionalIndex {
    const SESSION_HASH_SIZE: usize = SESSION_SUFFIX_LEN;

    /// The longest position a [FractionalKey] can carry once its session suffix is appended.
    const MAX_POSITION_LEN: usize = crate::collab::codec::MAX_POSITION_LEN;

    pub fn new(
        active: Vec<Entry>,
        moved: Vec<Entry>,
        suffix: [u8; Self::SESSION_HASH_SIZE],
    ) -> Self {
        let watermark = Self::max_virtual_ordinal(&active).max(Self::max_virtual_ordinal(&moved));
        FractionalIndex {
            active,
            moved,
            suffix,
            watermark,
        }
    }

    fn max_virtual_ordinal(entries: &[Entry]) -> u32 {
        entries
            .iter()
            .filter_map(|e| virtual_ordinal(&e.key))
            .max()
            .unwrap_or(0)
    }

    /// Highest [virtual_key] ordinal this index has ever handed out. Never decreases.
    pub fn watermark(&self) -> u32 {
        self.watermark
    }

    /// The [virtual_key]s that have to be inserted before position `through` (1-based) is
    /// addressable, in order. Empty when the index already reaches that far.
    ///
    /// Ordinals continue past the watermark rather than filling gaps, so a virtual row that was
    /// deleted is never named again — its record would turn the insert into a revive. Reads only:
    /// the caller emits the keys as a patch and applies that.
    pub fn plan_virtual(&self, through: usize) -> Vec<FractionalKey> {
        let missing = through.saturating_sub(self.len());
        let from = self.watermark.max(self.implied_watermark());
        (1..=missing as u32)
            .map(|i| virtual_key(from + i))
            .collect()
    }

    /// The keys an insert of `count` elements before position `at` (0-based) takes, in order.
    /// If `at` points past the threshold of materialized keys, a series of virtual keys will be
    /// returned, followed by a `count` of session-specific fractional keys.
    pub fn plan_insert(&self, at: usize, count: usize) -> Vec<FractionalKey> {
        let mut keys = self.plan_virtual(at);
        let run: Vec<FractionalKey> = if at < self.len() {
            self.create_keys(at, count).collect()
        } else {
            let from = self.watermark.max(self.implied_watermark());
            let next = virtual_key(from + keys.len() as u32 + 1);
            let lo: &[u8] = match (keys.last(), self.active.last()) {
                (Some(key), _) => key.position(),
                (None, Some(e)) => e.key.position(),
                (None, None) => &[],
            };
            CreateKeys::between(self, lo, next.position(), count).collect()
        };
        if run.len() != count {
            return Vec::new(); // the gap cannot name the run
        }
        keys.extend(run);
        keys
    }

    /// The ordinal the highest *filed* position already stands for. A virtual key has to sort past
    /// every key in the index, and [Self::watermark] only counts the ones virtual mints handed out.
    fn implied_watermark(&self) -> u32 {
        let highest = match (self.active.last(), self.moved.last()) {
            (Some(a), Some(m)) => a.key.position().max(m.key.position()),
            (Some(a), None) => a.key.position(),
            (None, Some(m)) => m.key.position(),
            (None, None) => &[],
        };
        let prefix = highest.len().min(3); // virtual position is three bytes
        let mut buf = [0, 0, 0, 0];
        buf[1..(1 + prefix)].copy_from_slice(&highest[..prefix]);
        u32::from_be_bytes(buf) / 2
    }

    /// The identity of every element, in the order they sit in.
    pub fn view(&self) -> impl Iterator<Item = &FractionalKey> {
        self.active.iter().filter_map(|e| match e.moved() {
            None => Some(&e.key),
            source => source,
        })
    }

    pub fn len(&self) -> usize {
        self.active.len()
    }

    pub fn is_empty(&self) -> bool {
        self.active.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<&Entry> {
        self.active.get(index)
    }

    pub fn key(&self, index: usize) -> Option<&FractionalKey> {
        let e = self.active.get(index)?;
        e.moved().or(Some(&e.key))
    }

    /// The active index of the element `key` names, `None` when it is hidden.
    pub fn position_of(&self, key: &FractionalKey) -> Option<usize> {
        match self.resolve(key)?.1 {
            Slot::Active(i) => Some(i),
            Slot::Moved(_) => None,
        }
    }

    fn find(&self, key: &FractionalKey) -> Option<Slot> {
        match self.active.binary_search_by_key(&key, |e| &e.key) {
            Ok(i) => Some(Slot::Active(i)),
            Err(_) => (self.moved.binary_search_by_key(&key, |e| &e.key).ok()).map(Slot::Moved),
        }
    }

    fn entry(&self, slot: Slot) -> &Entry {
        match slot {
            Slot::Active(i) => &self.active[i],
            Slot::Moved(j) => &self.moved[j],
        }
    }

    fn entry_mut(&mut self, slot: Slot) -> &mut Entry {
        match slot {
            Slot::Active(i) => &mut self.active[i],
            Slot::Moved(j) => &mut self.moved[j],
        }
    }

    /// The identity record and the position record of the element `key` names (the same slot when
    /// it is not moved), `None` for an unknown or dangling key. `key` is the identity, its current
    /// destination, or a position the element passed through.
    fn resolve(&self, key: &FractionalKey) -> Option<(Slot, Slot)> {
        let slot = self.find(key)?;
        let e = self.entry(slot);
        let Some(other) = e.moved() else {
            return Some((slot, slot)); // an identity on its own key, most common case
        };
        let other_slot = self.find(other)?;
        let o = self.entry(other_slot);
        if o.moved() != Some(&e.key) {
            // `key` is a position the element passed through, `other` its identity.
            let position = match o.moved() {
                Some(dest) => self.find(dest).unwrap_or(other_slot),
                None => other_slot,
            };
            return Some((other_slot, position));
        }
        // An identity and the destination it sits on. Hidden, both are in `moved` space and the
        // identity is the one carrying the removal.
        Some(match (slot, other_slot) {
            (Slot::Active(_), _) => (other_slot, slot),
            (_, Slot::Active(_)) => (slot, other_slot),
            _ if e.is_removed() => (slot, other_slot),
            _ => (other_slot, slot),
        })
    }

    /// Returns a record by its `identity` key. It must be an identity key, and not a transitive
    /// key of a move destination. See also: [FractionalIndex::entry_by_key].
    pub(crate) fn entry_by_id(&self, identity: &FractionalKey) -> Option<&Entry> {
        self.find(identity).map(|slot| self.entry(slot))
    }

    /// Returns a record by its `key`, either identity or a transitive key of a move destination.
    pub(crate) fn entry_by_key(&self, key: &FractionalKey) -> Option<&Entry> {
        self.resolve(key).map(|(slot, _)| self.entry(slot))
    }

    /// Raises `identity`'s touch stamp; `identity` must be an identity key. Returns whether that
    /// changed its visibility, and its removal stamp (zero for an unknown key).
    pub(crate) fn touch(&mut self, identity: &FractionalKey, at: Hlc) -> (bool, Hlc) {
        let Some(slot) = self.find(identity) else {
            return (false, Hlc::new(0));
        };
        let e = self.entry_mut(slot);
        let was_visible = e.is_visible();
        e.touched_at = e.touched_at.max(at);
        let removed_at = e.removed_at;

        if e.is_visible() == was_visible {
            (false, removed_at) // no visible effect
        } else {
            self.settle(identity, None);
            (true, removed_at)
        }
    }

    /// The oldest `moved_at` on record: a touch no newer than it is already outranked by every
    /// element's own insert or move.
    pub(crate) fn moved_floor(&self) -> Hlc {
        let stamps = self.active.iter().chain(&self.moved).map(|e| e.moved_at);
        stamps.min().unwrap_or(Hlc::new(0))
    }

    /// The key of the position `identity`'s element holds, `None` when it holds none.
    pub(crate) fn held_key(&self, identity: &FractionalKey) -> Option<FractionalKey> {
        let i = self.position_of(identity)?;
        Some(self.active[i].key.clone())
    }

    /// Plan move operation (moving range of elements under new position) without actually applying
    /// anything. Only generate necessary [FractionalKey]s, that can be later applied
    /// via [FractionalIndex::apply_move].
    pub fn plan_move<R: RangeBounds<usize>>(
        &self,
        source: R,
        dest: usize,
    ) -> Vec<(FractionalKey, FractionalKey)> {
        let start = match source.start_bound() {
            Bound::Included(&i) => i,
            Bound::Excluded(&i) => i + 1,
            Bound::Unbounded => 0,
        };
        let end = match source.end_bound() {
            Bound::Included(&i) => i + 1,
            Bound::Excluded(&i) => i,
            Bound::Unbounded => self.active.len(),
        };
        let l = self.active.len();
        // Rows past the tail are named rather than built, off the base `plan_virtual` mints from:
        // the caller's own call hands back the very keys this plans over.
        let from = self.watermark.max(self.implied_watermark());
        let eff = l.max(end.max(dest));
        let end = end.min(eff);
        if start == dest || start >= end || dest > eff {
            return Vec::new(); // no op
        }
        let len = end - start;

        // we precompute virtual key position for potential lower & upper bounds since it's cheap.
        // Tail index `i >= l` stands for ordinal `from + (i - l + 1)`: `dest - 1` for lo, `dest` for hi.
        let lo_position = (2 * (from + (dest.saturating_sub(l)) as u32)).to_be_bytes();
        let hi_position = (2 * (from + ((dest + 1).saturating_sub(l)) as u32)).to_be_bytes();

        let lo: &[u8] = if dest > 0 {
            match self.active.get(dest - 1) {
                None => &lo_position[1..],
                Some(e) => e.key.position(),
            }
        } else {
            [].as_ref()
        };
        let hi: &[u8] = if dest < eff {
            match self.active.get(dest) {
                None => &hi_position[1..],
                Some(e) => e.key.position(),
            }
        } else {
            [].as_ref()
        };

        let keys: Vec<FractionalKey> = CreateKeys::between(self, lo, hi, len).collect();
        if keys.len() != len {
            return Vec::new(); // the gap cannot name the run
        }
        (start..end)
            .map(|i| match self.active.get(i) {
                Some(e) => e.identity().clone(),
                None => virtual_key(from + (i - l + 1) as u32),
            })
            .zip(keys)
            .collect()
    }

    /// Moves the elements at `source` before `dest`, one [`Hlc`] for the whole run.
    ///
    /// A local move is a planned one applied to itself: [`Self::plan_move`] then
    /// [`Self::apply_move`], the same path a replicated move takes.
    ///
    /// A plan reaching past the tail names identities this index has never inserted, which
    /// [`Self::apply_move`] drops: a local move wants rows that are materialized already.
    pub fn move_to<R: RangeBounds<usize>>(&mut self, source: R, dest: usize) {
        let at = Hlc::now();
        for (identity, dest) in self.plan_move(source, dest) {
            self.apply_move(&identity, dest, at);
        }
    }

    pub fn remove_key(&mut self, key: &FractionalKey) -> Option<FractionalKey> {
        self.remove_key_at(key, Hlc::now())
    }

    /// [`Self::remove_key_at`] for each of `keys`.
    pub fn remove_keys_at(&mut self, keys: &[FractionalKey], at: Hlc) {
        let mut keys: Vec<&FractionalKey> = keys.iter().collect();
        keys.sort_unstable();
        keys.dedup();
        let (mut hidden, mut rest) = (Vec::new(), Vec::new());
        for key in keys {
            //TODO: optimise, since keys are sorted we don't need to search for entire active space
            // we can just search over slice since the last index found
            match self.active.binary_search_by_key(&key, |e| &e.key) {
                Ok(i) if self.active[i].moved.is_empty() => {
                    let e = &mut self.active[i];
                    e.removed_at = e.removed_at.max(at); // bump tombstone
                    if !e.is_visible() {
                        hidden.push(i);
                    }
                }
                _ => rest.push(key),
            }
        }
        let deactivated = hidden.iter().map(|&i| self.active[i].clone()).collect();
        Self::remove_all(&mut self.active, &hidden);
        Self::insert_all(&mut self.moved, deactivated);
        for key in rest {
            self.remove_key_at(key, at);
        }
    }

    /// [`Self::remove_key`] stamping `at` rather than the local clock: the apply path passes the
    /// commit's stamp, so every replica files the same removal.
    ///
    /// Raises the element's tombstone; its position register is left alone, so an insert or
    /// move newer than `at` puts it back where it last was. Returns the identity it answered to
    /// when this hid the element, `None` otherwise.
    pub fn remove_key_at(&mut self, key: &FractionalKey, at: Hlc) -> Option<FractionalKey> {
        let Some((slot, _)) = self.resolve(key) else {
            // Kept until the insert arrives, so the removal still outranks older writes.
            let mut e = Entry::new(key.clone(), Hlc::new(0), FractionalKey::NULL);
            e.removed_at = at;
            if let Some(ordinal) = virtual_ordinal(key) {
                self.watermark = self.watermark.max(ordinal);
            }
            self.insert_moved(e);
            return None;
        };
        let e = self.entry_mut(slot);
        let was_visible = e.is_visible(); // was entry visible before tombstone bump?
        e.removed_at = e.removed_at.max(at);
        let now_hidden = !e.is_visible(); // did tombstone bump make entry hidden?
        let identity = e.key.clone();
        self.settle(&identity, None);
        // return identity if our removal changed visibility
        (was_visible && now_hidden).then_some(identity)
    }

    /// The *positions* of the stored keys bracketing index `i`, session suffix stripped. An empty
    /// slice means "unbounded on that side".
    ///
    /// Stripping is what [FractionalKey]'s two-part order asks for: positions are compared on their
    /// own, so a position generated strictly between these two slices sorts strictly between the two
    /// stored keys whatever session minted any of them. Comparing against the full stored keys does
    /// not work — the session bytes would join the comparison at a depth where they mean nothing.
    ///
    /// Generated positions are never empty, so an empty slice is unambiguous.
    fn neighbours(index: &[Entry], i: usize) -> Option<(&[u8], &[u8])> {
        if i > index.len() {
            return None;
        }
        let left = if i == 0 {
            [].as_ref()
        } else {
            index[i - 1].key.position()
        };
        let right = index.get(i).map(|e| e.key.position()).unwrap_or(&[]);
        Some((left, right))
    }

    /// Generate a new [FractionalKey] that matches a given index. Return that key and an alias to it.
    ///
    /// Returns `None` if `index` is out of range, or if the generated key would exceed
    /// [MAX_KEY_LEN] — the position is too crowded to name.
    pub fn create_key(&mut self, index: usize) -> Option<&FractionalKey> {
        let (left, right) = Self::neighbours(&self.active, index)?;
        let mut buf = Self::create_fractional_key(left, right, InsertStrategy::Middle);
        buf.extend_from_slice(self.suffix.as_ref());
        let key = FractionalKey::try_from_bytes(&buf).ok()?;
        // A fresh key is both the element's position and its identity, so it carries no origin.
        self.active
            .insert(index, Entry::new(key, Hlc::now(), FractionalKey::NULL));
        Some(&self.active[index].key)
    }

    /// Insert an externally minted `key` at its sorted position, or put the element it names back
    /// onto it.
    ///
    /// Returns `None` when nothing moved: the key already names a live element, or the insert is not
    /// strictly newer than the write it races — so a delete wins over a concurrent insert of the
    /// same key, and redelivery of the original insert cannot resurrect.
    pub fn insert_key(&mut self, key: FractionalKey) -> Option<usize> {
        self.insert_key_at(key, Hlc::now())
    }

    /// [`Self::insert_key`] stamping `at` instead of reading the local clock — see
    /// [`Self::remove_key_at`].
    ///
    /// An insert of a key this index has seen is a move of its element onto it: it undoes a removal,
    /// and it takes the element back from a destination an older move sent it to.
    pub fn insert_key_at(&mut self, key: FractionalKey, at: Hlc) -> Option<usize> {
        // Before the ever-seen check: a rejected key was still handed out, and its ordinal must not
        // be minted again.
        if let Some(ordinal) = virtual_ordinal(&key) {
            self.watermark = self.watermark.max(ordinal);
        }
        match self.resolve(&key) {
            // it's a new entry
            None => {
                let index = self.active_index(&key);
                self.active
                    .insert(index, Entry::new(key, at, FractionalKey::NULL));
                Some(index)
            }
            Some((slot, position)) => {
                let e = self.entry(slot);
                let redundant = e.is_visible() && *e.moved().unwrap_or(&e.key) == key;
                // An index only for an insert that put the element here.
                self.write_position(slot, position, &key, at)
                    .filter(|_| !redundant)
            }
        }
    }

    /// [`Self::insert_key_at`] for each of `keys`. Returns whether any of them put back an element
    /// this index had already seen (a revive).
    pub fn insert_keys_at(&mut self, keys: &[FractionalKey], at: Hlc) -> bool {
        let (mut fresh, mut seen) = (Vec::new(), Vec::new());
        for key in keys {
            if let Some(ordinal) = virtual_ordinal(key) {
                self.watermark = self.watermark.max(ordinal);
            }
            if self.resolve(key).is_none() {
                fresh.push(key);
            } else {
                seen.push(key);
            }
        }
        fresh.sort_unstable();
        fresh.dedup();
        let entries = fresh
            .into_iter()
            .map(|key| Entry::new(key.clone(), at, FractionalKey::NULL))
            .collect();
        Self::insert_all(&mut self.active, entries);
        let mut revived = false;
        for key in seen {
            revived |= self.insert_key_at(key.clone(), at).is_some();
        }
        revived
    }

    /// Replays an author-minted move: `source`'s element takes the `dest` position, or keeps what it
    /// has if a newer write to its register already carried. Taking back a position it passed
    /// through is what makes moves invertible.
    ///
    /// Concurrent moves of one element order by `(at, dest)`; the loser's `dest` is still filed as a
    /// position the element passed through, keeping both peers' `moved` spaces identical.
    pub fn apply_move(&mut self, source: &FractionalKey, dest: FractionalKey, at: Hlc) {
        let Some((slot, position)) = self.resolve(source) else {
            return; // a key this index has never seen
        };
        self.write_position(slot, position, &dest, at);
    }

    /// Writes `{at → dest}` (null for its own key) into the identity record at `id`, files `dest` as
    /// a position it names win or lose, and moves `position` out of `active` if it lost its place.
    /// Every insert and move is this one join. Returns the active index if it won and is visible.
    fn write_position(
        &mut self,
        id: Slot,
        position: Slot,
        dest: &FractionalKey,
        at: Hlc,
    ) -> Option<usize> {
        let null = FractionalKey::NULL;
        let e = self.entry_mut(id);
        let to_self = e.key == *dest; // are we updating existing entry directly?
        let updated = e.write_position(at, if to_self { &null } else { dest }); // did we update the entry
        let visible = e.is_visible();
        let identity = (!to_self).then(|| e.key.clone());
        // returns slot where `dest` key entry should be updated or inserted
        let filed = match &identity {
            None => Ok(id),
            Some(_) if self.entry(position).key == *dest => Ok(position),
            Some(_) => match self.active.binary_search_by_key(&dest, |e| &e.key) {
                Ok(i) => Ok(Slot::Active(i)),
                Err(k) => match self.moved.binary_search_by_key(&dest, |e| &e.key) {
                    Ok(j) => Ok(Slot::Moved(j)),
                    Err(m) => Err((k, m)),
                },
            },
        };
        if let (Some(identity), Ok(slot)) = (&identity, filed) {
            self.entry_mut(slot).write_position(at, identity);
        }
        // A losing write leaves the identity record as it was, and a winning one never hides it.
        let (new, k) = match filed {
            Ok(Slot::Active(i)) => return updated.then_some(i), // everything already done
            Ok(Slot::Moved(_)) if !updated || !visible => return None, // loosing update
            Ok(Slot::Moved(j)) => (self.moved.remove(j), None), // moved -> active
            Err((k, m)) => {
                // insert new entry
                let new = Entry::new(dest.clone(), at, identity.unwrap_or_default());
                if !updated || !visible {
                    self.moved.insert(m, new);
                    return None;
                }
                (new, Some(k))
            }
        };
        let k = k.unwrap_or_else(|| self.active_index(&new.key)); //TODO: should it even happen?
        let Slot::Active(i) = position else {
            self.active.insert(k, new);
            return Some(k);
        };
        // The old position leaves `active` as the new one enters: one shift of the span between.
        let old = std::mem::replace(&mut self.active[i], new);
        let k = if k > i {
            self.active[i..k].rotate_left(1);
            k - 1
        } else {
            self.active[k..=i].rotate_right(1);
            k
        };
        self.insert_moved(old);
        Some(k)
    }

    fn settle(&mut self, identity: &FractionalKey, old: Option<&FractionalKey>) -> bool {
        let Some(slot) = self.find(identity) else {
            return false;
        };
        let e = self.entry(slot);
        let visible = e.is_visible();
        let position = e.moved().unwrap_or(identity).clone();
        let mut changed = match old {
            Some(old) if *old != position => self.deactivate(old),
            _ => false,
        };
        changed |= if visible {
            self.activate(&position)
        } else {
            self.deactivate(&position)
        };
        changed
    }

    /// Moves the active record filed under `key`, if any, into `moved` space unchanged.
    fn deactivate(&mut self, key: &FractionalKey) -> bool {
        let Ok(i) = self.active.binary_search_by_key(&key, |e| &e.key) else {
            return false;
        };
        let e = self.active.remove(i);
        self.insert_moved(e);
        true
    }

    /// Moves the record filed under `key` in `moved` space, if any, into `active`.
    fn activate(&mut self, key: &FractionalKey) -> bool {
        let Ok(j) = self.moved.binary_search_by_key(&key, |e| &e.key) else {
            return false;
        };
        let e = self.moved.remove(j);
        let i = self.active_index(&e.key);
        self.active.insert(i, e);
        true
    }

    /// Where `key` would sit among the active entries, whether or not it is one of them.
    pub fn active_index(&self, key: &FractionalKey) -> usize {
        match self.active.binary_search_by_key(&key, |e| &e.key) {
            Ok(i) | Err(i) => i,
        }
    }

    /// Returns an iterator yielding a run of `count` new [FractionalKey]s for the gap at `start`,
    /// one per [Iterator::next] call. It reads the index but does not touch it — the caller inserts
    /// whatever it takes.
    ///
    /// The run is planned against `count` up front, so the keys come out as short as the gap allows
    /// (see [CreateKeys]). It yields fewer than `count` keys only when the gap cannot hold them.
    pub fn create_keys(&self, start: usize, count: usize) -> CreateKeys {
        CreateKeys::new(self, start, count)
    }

    /// Creates a new key payload which is lexically higher than `lo` and lower than `hi`. Returned
    /// as a [KeyBuf] because callers still have the session suffix to append before sealing it into
    /// a [FractionalKey].
    fn create_fractional_key(lo: &[u8], hi: &[u8], strategy: InsertStrategy) -> KeyBuf {
        let mut key = KeyBuf::new();
        // Once we place a digit strictly below `hi`, the rest of `hi` no longer constrains us and
        // the upper bound effectively becomes +infinity (digit 256).
        let mut hi_unbounded = hi.is_empty();
        let mut i = 0;
        loop {
            // `lo` shorter than the key we build is padded with zeroes (its smallest continuation).
            let lo_digit = lo.get(i).copied().unwrap_or(0) as u16;
            let hi_digit = if hi_unbounded { 256 } else { hi[i] as u16 };

            if hi_digit - lo_digit >= 2 {
                // There is room for a digit strictly between the two bounds: pick the midpoint.
                key.push(strategy.next_byte(lo_digit, hi_digit));
                return key;
            }

            // The digits are equal (shared prefix) or adjacent (no room here): keep the `lo` digit
            // and descend into the next position.
            key.push(lo_digit as u8);
            if hi_digit != lo_digit {
                // We just placed a digit below `hi`, so the upper bound stops constraining us.
                hi_unbounded = true;
            }
            i += 1;
        }
    }

    /// Every shown element's position record, in order.
    pub fn iter(&self) -> impl Iterator<Item = &Entry> + '_ {
        self.active.iter()
    }

    /// Removes the entries at `indices` (ascending, unique) in one compacting pass.
    fn remove_all(space: &mut Vec<Entry>, indices: &[usize]) {
        if indices.is_empty() {
            return;
        }
        let mut next = 0;
        let mut write = 0;
        for read in 0..space.len() {
            if indices.get(next) == Some(&read) {
                next += 1;
                continue;
            }
            space.swap(write, read);
            write += 1;
        }
        space.truncate(write);
    }

    /// Merges `entries` — ascending by key, none of them already filed — into `space` from the back,
    /// so each entry already there moves at most once.
    fn insert_all(space: &mut Vec<Entry>, mut entries: Vec<Entry>) {
        if entries.is_empty() {
            return;
        }
        space.reserve_exact(entries.len());
        space.extend(entries.iter().cloned()); // grows once; these slots are all overwritten below
        let mut write = space.len();
        let mut read = write - entries.len();
        while let Some(e) = entries.pop() {
            while read > 0 && space[read - 1].key > e.key {
                write -= 1;
                read -= 1;
                space.swap(write, read);
            }
            write -= 1;
            space[write] = e;
        }
    }

    /// Files `e` in `moved` space, replacing whatever was already filed under its key.
    ///
    /// `moved` is kept sorted by key — every lookup in here binary-searches it — so a record goes
    /// where the search says it goes, not on the end.
    fn insert_moved(&mut self, e: Entry) {
        match self.moved.binary_search_by_key(&&e.key, |o| &o.key) {
            Ok(i) => self.moved[i] = e,
            Err(i) => self.moved.insert(i, e),
        }
    }

    /// The whole index as bytes: a version byte, then each space as a column table.
    ///
    /// The two spaces are written back to back and read back the same way, so the split between them
    /// costs nothing beyond each table's own entry count. See [codec](crate::collab::codec) for the
    /// layout and for why an index is worth encoding by column rather than by entry.
    pub fn encode(&self) -> Result<Vec<u8>, CodecError> {
        let mut out = Vec::new();
        out.push(FORMAT_VERSION);
        encode_entries(&self.active, &mut out)?;
        encode_entries(&self.moved, &mut out)?;
        Ok(out)
    }

    /// Reads back what [Self::encode] wrote.
    ///
    /// `suffix` is the **local** session's, not the one that wrote the bytes: it is what this replica
    /// will mint new keys with, and it has to differ from every peer's or two replicas generate
    /// colliding keys. Nothing in the payload names it, deliberately — a snapshot is restored by
    /// whichever replica loads it, and it is that replica's identity that matters.
    pub fn decode(bytes: &[u8], suffix: [u8; Self::SESSION_HASH_SIZE]) -> Result<Self, CodecError> {
        let (&version, mut input) = bytes.split_first().ok_or(CodecError::UnexpectedEof)?;
        if version != FORMAT_VERSION {
            return Err(CodecError::UnsupportedVersion(version));
        }
        let active = decode_entries(&mut input)?;
        let moved = decode_entries(&mut input)?;
        if !input.is_empty() {
            return Err(CodecError::TrailingBytes(input.len()));
        }
        // Through `new`, so the watermark is re-derived rather than carried in the payload.
        Ok(FractionalIndex::new(active, moved, suffix))
    }
}

/// The columnar encoding is the representation in *every* serde format, human-readable ones
/// included: an index is bulk machine state, and there is no readable rendering of a few dozen bytes
/// standing in for ten thousand keys that would be worth a second code path to maintain.
///
/// [Entry] keeps its own derive, so a legible dump of an index's contents is still a `{:?}` or a
/// `serde_json::to_string` over [FractionalIndex::iter] away.
impl Serialize for FractionalIndex {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let bytes = self.encode().map_err(serde::ser::Error::custom)?;
        serializer.serialize_bytes(&bytes)
    }
}

impl<'de> Deserialize<'de> for FractionalIndex {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_bytes(FractionalIndexVisitor)
    }
}

/// Accepts every shape a format may hand the payload over in: borrowed bytes, an owned buffer, or a
/// sequence of `u8`. Which one it is depends on the format — bitcode calls `visit_bytes`, others hand
/// over an owned buffer, and a format without native byte support (serde_json among them) renders
/// `serialize_bytes` as a sequence.
///
/// The session suffix is not in the payload, so a deserialized index comes back with a zeroed one,
/// exactly as it did under `#[serde(skip)]`. A replica that means to *mint* keys through the index
/// has to come in through [FractionalIndex::decode] with its own session instead.
struct FractionalIndexVisitor;

impl<'de> Visitor<'de> for FractionalIndexVisitor {
    type Value = FractionalIndex;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "an encoded fractional index, as a byte sequence")
    }

    fn visit_bytes<E: serde::de::Error>(self, v: &[u8]) -> Result<Self::Value, E> {
        FractionalIndex::decode(v, Default::default()).map_err(E::custom)
    }

    fn visit_byte_buf<E: serde::de::Error>(self, v: Vec<u8>) -> Result<Self::Value, E> {
        self.visit_bytes(&v)
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut bytes = Vec::with_capacity(seq.size_hint().unwrap_or(0));
        while let Some(b) = seq.next_element::<u8>()? {
            bytes.push(b);
        }
        self.visit_bytes(&bytes)
    }
}

/// bitcode coders delegating to [FractionalIndex::encode]/[FractionalIndex::decode], the same
/// columnar payload the serde impls carry — written by hand for the same reason as
/// [`FractionalKeyEncoder`](crate::collab::fractional_key::FractionalKeyEncoder), and coming back
/// with a zeroed session suffix for the same reason too.
#[derive(Default)]
pub struct FractionalIndexEncoder(<[u8] as Encode>::Encoder);

impl Buffer for FractionalIndexEncoder {
    fn collect_into(&mut self, out: &mut Vec<u8>) {
        self.0.collect_into(out);
    }

    fn reserve(&mut self, additional: NonZeroUsize) {
        self.0.reserve(additional);
    }
}

impl Encoder<FractionalIndex> for FractionalIndexEncoder {
    #[inline]
    #[allow(clippy::expect_used)]
    fn encode(&mut self, t: &FractionalIndex) {
        let bytes = t.encode().expect("fractional index cannot be encoded");
        Encoder::<[u8]>::encode(&mut self.0, &bytes);
    }
}

impl Encode for FractionalIndex {
    type Encoder = FractionalIndexEncoder;
}

#[derive(Default)]
pub struct FractionalIndexDecoder<'a>(<Vec<u8> as Decode<'a>>::Decoder);

impl<'a> View<'a> for FractionalIndexDecoder<'a> {
    fn populate(&mut self, input: &mut &'a [u8], length: usize) -> bitcode::__private::Result<()> {
        self.0.populate(input, length)
    }
}

impl<'a> Decoder<'a, FractionalIndex> for FractionalIndexDecoder<'a> {
    /// # Panics
    ///
    /// On a malformed payload: bitcode wants all validation in [`View::populate`], which cannot see
    /// the entry tables. Untrusted input should come in through `serde`, which reports the error.
    #[inline]
    #[allow(clippy::expect_used)]
    fn decode(&mut self) -> FractionalIndex {
        let bytes: Vec<u8> = self.0.decode();
        FractionalIndex::decode(&bytes, Default::default()).expect("malformed bitcode payload")
    }
}

impl<'a> Decode<'a> for FractionalIndex {
    type Decoder = FractionalIndexDecoder<'a>;
}

enum InsertStrategy {
    Middle,
}

impl InsertStrategy {
    #[inline]
    pub fn next_byte(&self, lo: u16, hi: u16) -> u8 {
        match self {
            InsertStrategy::Middle => (lo + (hi - lo) / 2) as u8,
        }
    }
}

/// How many positions of exactly `width` digits sort strictly between `lo` and `hi`, an empty `hi`
/// meaning unbounded. Saturates once the answer is far past any run length.
///
/// A run reads its gap as a range of integers: `lo` and `hi` padded (or truncated) to `width` digits
/// and read base-256 as `L` and `H`, with `H = 256^width` when unbounded. Every width-`width` `X`
/// with `L < X < H` sorts strictly between `lo` and `hi`, whichever bound is longer or shorter than
/// the width. Strictness is load-bearing at the bottom end: it drops `X = lo ++ [0x00…]`, and since
/// nothing sorts between `p` and `p ++ [0x00]`, emitting that would seal off the gap above it.
///
/// Capacity never shrinks as `width` grows, which is what makes "the narrowest width that fits" well
/// defined: with `D = H - L`, each further digit gives `D' = 256·D + (hi_digit - lo_digit)`, so a
/// positive `D` stays positive and a negative one stays negative.
fn gap_capacity(lo: &[u8], hi: &[u8], width: usize) -> u128 {
    let unbounded = hi.is_empty();
    let mut diff: i128 = 0;
    for i in 0..width {
        // `256^width - 1` is `[0xff; width]`, so an unbounded `hi` is all-`0xff` digits with the
        // missing `+ 1` folded into the result below.
        let hi_digit = if unbounded {
            0xff
        } else {
            hi.get(i).copied().unwrap_or(0) as i128
        };
        let lo_digit = lo.get(i).copied().unwrap_or(0) as i128;
        diff = (diff * 256 + hi_digit - lo_digit).min(u64::MAX as i128);
        if diff < 0 {
            return 0; // `lo` sorts above `hi`: not a gap, at this width or any wider one
        }
    }
    // A bounded `hi` is a position itself and is excluded; an unbounded one is `[0xff; width] + 1`,
    // so its topmost position is already counted.
    (if unbounded { diff } else { diff - 1 }).max(0) as u128
}

/// Adds `delta` to a big-endian position in place. The width is picked to hold the whole run, so a
/// carry running off the front is a bug rather than something to handle.
fn add_assign(position: &mut [u8], delta: u8) {
    let mut carry = delta as u16;
    for digit in position.iter_mut().rev() {
        if carry == 0 {
            return;
        }
        let sum = *digit as u16 + carry;
        *digit = sum as u8;
        carry = sum >> 8;
    }
}

/// Iterator produced by [FractionalIndex::create_keys]: a run of new [FractionalKey]s for one gap,
/// minted lazily but planned eagerly.
///
/// Knowing the run length up front is what keeps the keys short. The width that holds the whole run
/// is picked once, and the run is then a fixed-width counter over it — so every key in a run is the
/// same length, and whether the run stays inline is settled before the first [Iterator::next]
/// instead of being discovered part-way through it.
pub struct CreateKeys {
    suffix: [u8; FractionalIndex::SESSION_HASH_SIZE],
    /// The position to yield next, as many digits as the run was planned for.
    next: KeyBuf,
    /// Distance between consecutive positions of the run.
    stride: u8,
    remaining: usize,
}

impl CreateKeys {
    /// Width [CreateKeys] pads its positions out to.
    ///
    /// A position only counts up to `0xff` per byte before it has to grow, so a narrow one runs out of
    /// room fast — but padding is free up to this point, since a key stays a single word until the
    /// position plus its session suffix outgrows [INLINE_CAP]. Three bytes hold ~16.7M positions in one
    /// gap; one byte holds 255.
    const RUN_WIDTH: usize = INLINE_CAP - SESSION_SUFFIX_LEN;

    #[allow(clippy::expect_used)]
    fn new(index: &FractionalIndex, i: usize, count: usize) -> Self {
        let (lo, hi) = FractionalIndex::neighbours(&index.active, i)
            .expect("cannot mint fractional keys past the end of the index");
        Self::between(index, lo, hi, count)
    }

    /// [`Self::new`] for a gap the caller brackets: a gap reaching past the tail has no active
    /// neighbour to read. Identical to [`Self::new`] when both bounds do come from `active`.
    fn between<'a>(index: &'a FractionalIndex, lo: &'a [u8], hi: &[u8], count: usize) -> Self {
        // A record in `moved` space sitting in the gap raises its floor: its key already names an
        // element, so re-minting it would address that one — reviving it, at worst — instead of
        // creating one.
        let lo = index.moved.iter().fold(lo, |floor, e| {
            let position = e.key.position();
            if position > floor && (hi.is_empty() || position < hi) {
                position
            } else {
                floor
            }
        });
        // A gap without room for the run leaves `remaining` at zero, so the iterator ends where the
        // room does rather than minting keys that do not fit in it.
        let (next, stride, remaining) = match Self::plan(lo, hi, count) {
            Some((next, stride)) => (next, stride, count),
            None => (KeyBuf::new(), 1, 0),
        };
        CreateKeys {
            suffix: index.suffix,
            next,
            stride,
            remaining,
        }
    }

    /// The first position and stride of a run of `count` keys between `lo` and `hi`, or `None` if no
    /// width up to [MAX_POSITION_LEN] has room for it.
    pub(crate) fn plan(lo: &[u8], hi: &[u8], count: usize) -> Option<(KeyBuf, u8)> {
        // Capacity grows with width, so the first width that fits is the narrowest one. Widening
        // past it to [RUN_WIDTH] is free — the key is one word either way — and pays for the stride.
        let width = (1..=FractionalIndex::MAX_POSITION_LEN)
            .find(|&width| gap_capacity(lo, hi, width) >= count as u128)?
            .max(Self::RUN_WIDTH);
        // A stride of 2 leaves a free position between consecutive keys, so a later insert between
        // two of them lands at this same width — which at [RUN_WIDTH] is the difference between an
        // inline key and a heap allocation.
        let stride = if gap_capacity(lo, hi, width) > 2 * count as u128 {
            2
        } else {
            1
        };
        // The run starts one stride above the gap's floor and ends `count` strides later, which is
        // exactly what the width was chosen to accommodate.
        let mut next = KeyBuf::from(&lo[..lo.len().min(width)]);
        next.resize(width, 0);
        add_assign(&mut next, stride);
        Some((next, stride))
    }
}

impl Iterator for CreateKeys {
    type Item = FractionalKey;

    /// Yields `None` once the planned run is used up — immediately, for a gap with no room for it.
    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        let mut buf = self.next.clone();
        buf.extend_from_slice(self.suffix.as_ref());

        add_assign(&mut self.next, self.stride);

        // Infallible: the width is capped so that the suffix still fits within [MAX_KEY_LEN].
        FractionalKey::try_from_bytes(&buf).ok()
    }
}

#[cfg(test)]
mod test {
    #![allow(clippy::unwrap_used)]
    use super::{
        gap_capacity, virtual_key, virtual_ordinal, Entry, FractionalIndex, FractionalKey, Hlc,
        Slot,
    };
    use std::collections::HashSet;

    /// The identity of every entry, in stored order. An identity is stable per element across a
    /// `move_to`, so this tracks element movement *within* a single [FractionalIndex].
    fn identity_order(fi: &FractionalIndex) -> Vec<FractionalKey> {
        fi.view().cloned().collect()
    }

    /// The newest removal of the element `key` names, `None` when it was never removed.
    fn removed_at(fi: &FractionalIndex, key: &FractionalKey) -> Option<Hlc> {
        let e = fi.entry(fi.resolve(key)?.0);
        (e.removed_at > Hlc::new(0)).then_some(e.removed_at)
    }

    /// A wall-clock millisecond in the past — Sept 2020, below the Nov 2022 constant
    /// [`crate::mock_time`] serves under `cfg(test)`. A stamp from the future would become the
    /// process-global high watermark and drag every concurrent test's `Hlc::now()` with it.
    const PAST: Hlc = Hlc::new(1_600_000_000_000 << 16);

    /// A stamp `step` counter ticks above [`PAST`], still inside the same millisecond.
    fn at(step: u64) -> Hlc {
        Hlc::new(PAST.get() + step)
    }

    /// An index of `count` virtual keys, all stamped `at(1)`.
    fn virtual_index(count: u32) -> (FractionalIndex, Vec<FractionalKey>) {
        let mut fi = FractionalIndex::new(vec![], vec![], [b'a', 0, 0, 0]);
        let keys: Vec<FractionalKey> = (1..=count).map(virtual_key).collect();
        for key in &keys {
            fi.insert_key_at(key.clone(), at(1));
        }
        (fi, keys)
    }

    /// `moved` records no active entry's chain reaches: exactly the removed elements' records.
    fn unreachable(fi: &FractionalIndex) -> Vec<FractionalKey> {
        fi.moved
            .iter()
            .filter(|e| fi.position_of(&e.key).is_none())
            .map(|e| e.key.clone())
            .collect()
    }

    #[test]
    fn plan_insert_past_the_tail() {
        let (mut fi, keys) = virtual_index(2); // [v1, v2]
        let ordinals = |keys: &[FractionalKey]| -> Vec<Option<u32>> {
            keys.iter().map(virtual_ordinal).collect()
        };

        // Inside the index: nothing to materialize
        let inside = fi.plan_insert(1, 2); // [v1, s1, s2, v2]
        assert_eq!(ordinals(&inside), [None, None]);
        assert!(keys[0] < inside[0] && inside[0] < inside[1] && inside[1] < keys[1]);

        // Right after the last element: nothing to materialize either.
        let at_the_end = fi.plan_insert(2, 1); // [v1, v2, s1]
        assert_eq!(ordinals(&at_the_end), [None]);
        assert!(keys[1] < at_the_end[0] && at_the_end[0] < virtual_key(3));

        // Two elements before position 4: rows 3 and 4 are materialized
        let past = fi.plan_insert(4, 2); // [v1, v2, v3, v4, s1, s2]
        assert_eq!(ordinals(&past), [Some(3), Some(4), None, None]);
        assert!(virtual_key(4) < past[2] && past[2] < past[3] && past[3] < virtual_key(5));

        for key in &past {
            fi.insert_key_at(key.clone(), at(2));
        }
        // materialized: [v1, v2, v3, v4, s1, s2]
        assert_eq!(
            ordinals(&identity_order(&fi)),
            [Some(1), Some(2), Some(3), Some(4), None, None]
        );
        // The run's keys are longer than a virtual one, and the last in the index: the next
        // virtual key still sorts past them, and is the one the run was kept below.
        assert_eq!(fi.plan_virtual(7), [virtual_key(5)]);
    }

    /// A delete is invertible: an insert of the same key stamped past it puts the element back where
    /// it was, and nothing stamped before it does.
    #[test]
    fn undo_remove() {
        let (mut fi, keys) = virtual_index(3);
        assert_eq!(fi.remove_key_at(&keys[1], at(10)), Some(keys[1].clone()));
        assert_eq!(identity_order(&fi), vec![keys[0].clone(), keys[2].clone()]);
        assert_eq!(fi.position_of(&keys[1]), None);
        // Redelivery of the original insert, and a stamp equal to the delete's, leave it removed.
        assert_eq!(fi.insert_key_at(keys[1].clone(), at(1)), None);
        assert_eq!(fi.insert_key_at(keys[1].clone(), at(10)), None);
        assert_eq!(fi.len(), 2);
        // Strictly newer: back at the same position, under the same key.
        assert_eq!(fi.insert_key_at(keys[1].clone(), at(20)), Some(1));
        assert_eq!(identity_order(&fi), keys);
        assert_eq!(fi.get(1).unwrap().key, keys[1]);
        // Redelivered revival: nothing left to do.
        assert_eq!(fi.insert_key_at(keys[1].clone(), at(20)), None);
        assert_eq!(fi.len(), 3);

        // Delete and revival commute: whichever arrives first, the newer one decides.
        let (mut x, mut y) = (fi.clone(), fi.clone());
        x.remove_key_at(&keys[1], at(30));
        x.insert_key_at(keys[1].clone(), at(40));
        y.insert_key_at(keys[1].clone(), at(40));
        y.remove_key_at(&keys[1], at(30));
        assert_eq!(x, y);
        assert_eq!(identity_order(&x), keys);
    }

    /// A move is invertible, one hop at a time: each undo names the position the element held
    /// before, and a concurrent move settles by `(at, dest)` whichever order the two arrive in.
    #[test]
    fn undo_move() {
        let (mut fi, keys) = virtual_index(3);
        let identity = keys[0].clone();
        let d1 = fi.create_keys(2, 1).next().unwrap(); // between the second and third
        let d2 = fi.create_keys(3, 1).next().unwrap(); // past the end
        let middle = vec![keys[1].clone(), identity.clone(), keys[2].clone()];
        let end = vec![keys[1].clone(), keys[2].clone(), identity.clone()];

        fi.apply_move(&identity, d1.clone(), at(10));
        assert_eq!(identity_order(&fi), middle);
        let moved_away = fi.clone();

        // Moved back onto its own key: original position, original key.
        fi.apply_move(&identity, identity.clone(), at(20));
        assert_eq!(identity_order(&fi), keys);
        assert_eq!(fi.position_of(&identity), Some(0));
        assert_eq!(fi.get(0).unwrap().key, identity);
        // Redelivery of the undone move changes nothing.
        let settled = fi.clone();
        fi.apply_move(&identity, identity.clone(), at(20));
        assert_eq!(fi, settled);

        // The undo racing a newer move elsewhere, delivered in both orders.
        let (mut x, mut y) = (moved_away.clone(), moved_away);
        x.apply_move(&identity, identity.clone(), at(20));
        x.apply_move(&identity, d2.clone(), at(30));
        y.apply_move(&identity, d2.clone(), at(30));
        y.apply_move(&identity, identity.clone(), at(20));
        assert_eq!(x, y);
        // The later stamp holds the element.
        assert_eq!(identity_order(&x), end);
        assert_eq!(x.position_of(&identity), Some(2));
        assert_eq!(x.get(2).unwrap().key, d2);
        assert_eq!(x.position_of(&d1), Some(2)); // the position it passed through still finds it

        // Two hops, undone one at a time: `fi` sits back on its identity, stamped at(20).
        fi.apply_move(&identity, d1.clone(), at(30));
        assert_eq!(identity_order(&fi), middle);
        fi.apply_move(&identity, d2.clone(), at(40));
        assert_eq!(identity_order(&fi), end);
        // Undo the last move only: back to the first destination.
        fi.apply_move(&identity, d1.clone(), at(50));
        assert_eq!(identity_order(&fi), middle);
        assert_eq!(fi.get(1).unwrap().key, d1);
        // Undo the first one too: back where it started, under its own key.
        fi.apply_move(&identity, identity.clone(), at(60));
        assert_eq!(identity_order(&fi), keys);
        assert_eq!(fi.get(0).unwrap().key, identity);
        // Every position it passed through still resolves to it.
        for key in [&d1, &d2] {
            assert_eq!(fi.position_of(key), Some(0));
        }
    }

    /// A remove, its undo and a concurrent move of the same element race: whichever order the three
    /// reach a replica in, it has to end on the same records and the same readout.
    #[test]
    fn remove_move_races_commute() {
        let (fi, keys) = virtual_index(3);
        let k = keys[1].clone();
        let d = fi.create_keys(3, 1).next().unwrap(); // a destination a peer minted

        // The remove and its undo first, the move arriving late.
        let mut a = fi.clone();
        a.remove_key_at(&k, at(10));
        a.insert_key_at(k.clone(), at(40));
        a.apply_move(&k, d.clone(), at(30));

        // The move first: the remove and the undo meet an element that has moved on.
        let mut b = fi.clone();
        b.apply_move(&k, d.clone(), at(30));
        b.remove_key_at(&k, at(10));
        b.insert_key_at(k.clone(), at(40));

        // The move in between: it meets a removed element.
        let mut c = fi.clone();
        c.remove_key_at(&k, at(10));
        c.apply_move(&k, d.clone(), at(30));
        c.insert_key_at(k.clone(), at(40));

        assert_eq!(a, b);
        assert_eq!(a, c);
        // The newest write holds the element: it is back where it was inserted.
        for replica in [&a, &b, &c] {
            assert_eq!(identity_order(replica), keys);
            assert_eq!(replica.position_of(&d), Some(1));
        }
    }

    /// Ops name the key their author observed — the position the element held then, not its
    /// identity — so every key on a dead chain has to lead back to the same element.
    #[test]
    fn held_key_addressing_after_remove() {
        let (mut fi, keys) = virtual_index(2);
        let k = keys[0].clone();
        let d = fi.create_keys(2, 1).next().unwrap();
        fi.apply_move(&k, d.clone(), at(10));
        assert_eq!(fi.remove_key_at(&d, at(20)), Some(k.clone()));

        let once = fi.clone();
        // Redelivered remove by the same key must be a no-op.
        assert_eq!(fi.remove_key_at(&d, at(20)), None);
        assert_eq!(fi, once, "redelivered remove diverged");
        // Undo naming the observed position must revive the SAME element, not fork a new identity.
        fi.insert_key_at(d.clone(), at(30));
        assert!(
            fi.position_of(&k).is_some(),
            "identity forked: k no longer resolves"
        );
        assert_eq!(fi.position_of(&k), fi.position_of(&d));

        // The same, two hops along: the removal names the last of them.
        let (mut fi, keys) = virtual_index(3);
        let identity = keys[0].clone();
        let d1 = fi.create_keys(2, 1).next().unwrap();
        let d2 = fi.create_keys(3, 1).next().unwrap();
        fi.apply_move(&identity, d1.clone(), at(10));
        fi.apply_move(&identity, d2.clone(), at(20));
        assert_eq!(fi.remove_key_at(&d2, at(30)), Some(identity.clone()));
        let once = fi.clone();
        assert_eq!(fi.remove_key_at(&d2, at(30)), None);
        assert_eq!(fi, once, "redelivered remove diverged");
        // An undo naming a position it passed through puts that same element back on it.
        assert!(fi.insert_key_at(d1.clone(), at(40)).is_some());
        assert_eq!(
            identity_order(&fi),
            vec![keys[1].clone(), identity.clone(), keys[2].clone()]
        );
        for key in [&d1, &d2] {
            assert_eq!(fi.position_of(&identity), fi.position_of(key));
        }
    }

    /// An op is a join, so delivery order cannot matter. The hand-written races above check the
    /// orders someone thought of; this one checks every order of a racing set.
    #[test]
    fn ops_commute_in_all_orders() {
        #[derive(Clone, Debug)]
        enum Op {
            Remove(FractionalKey, Hlc),
            Insert(FractionalKey, Hlc),
            Move(FractionalKey, FractionalKey, Hlc),
            Touch(FractionalKey, Hlc),
        }

        fn apply(fi: &mut FractionalIndex, op: &Op) {
            match op {
                Op::Remove(key, at) => {
                    fi.remove_key_at(key, *at);
                }
                Op::Insert(key, at) => {
                    fi.insert_key_at(key.clone(), *at);
                }
                Op::Move(source, dest, at) => fi.apply_move(source, dest.clone(), *at),
                Op::Touch(key, at) => {
                    fi.touch(key, *at);
                }
            }
        }

        fn permutations(ops: &[Op]) -> Vec<Vec<Op>> {
            if ops.is_empty() {
                return vec![Vec::new()];
            }
            let mut out = Vec::new();
            for i in 0..ops.len() {
                let mut rest = ops.to_vec();
                let head = rest.remove(i);
                for mut tail in permutations(&rest) {
                    tail.insert(0, head.clone());
                    out.push(tail);
                }
            }
            out
        }

        /// Applies `ops` in every order; each must land on the same records, touch stamps and
        /// readout.
        fn settle(base: &FractionalIndex, ops: &[Op]) -> (FractionalIndex, Vec<FractionalKey>) {
            let touched = |fi: &FractionalIndex| -> Vec<Hlc> {
                fi.active
                    .iter()
                    .chain(&fi.moved)
                    .map(|e| e.touched_at)
                    .collect()
            };
            let mut expected: Option<(FractionalIndex, Vec<FractionalKey>)> = None;
            for order in permutations(ops) {
                let mut fi = base.clone();
                for op in &order {
                    apply(&mut fi, op);
                }
                let readout = identity_order(&fi);
                match &expected {
                    None => expected = Some((fi, readout)),
                    Some((first, first_readout)) => {
                        assert_eq!(&fi, first, "records diverged on {order:?}");
                        assert_eq!(touched(&fi), touched(first), "touch diverged on {order:?}");
                        assert_eq!(&readout, first_readout, "readout diverged on {order:?}");
                    }
                }
            }
            expected.unwrap()
        }

        let (base, keys) = virtual_index(3);
        let key = keys[1].clone();
        let mut gen = base.create_keys(3, 2);
        let (d1, d2) = (gen.next().unwrap(), gen.next().unwrap());
        drop(gen);
        // One element removed, undone, touched, and moved to two destinations by two peers.
        let ops = [
            Op::Remove(key.clone(), at(10)),
            Op::Move(key.clone(), d1.clone(), at(30)),
            Op::Move(key.clone(), d2.clone(), at(35)),
            Op::Insert(key.clone(), at(40)),
            Op::Touch(key.clone(), at(20)),
        ];
        // The newest write holds the element, and every destination is filed as passed through.
        let (fi, readout) = settle(&base, &ops);
        assert_eq!(readout, keys);
        assert_eq!(fi.moved.len(), 2);

        // A moved element removed: a removal tying with a move takes the element out.
        let moved = [
            Op::Move(key.clone(), d1, at(10)),
            Op::Remove(key.clone(), at(20)),
            Op::Move(key.clone(), d2.clone(), at(20)),
        ];
        let hidden = vec![keys[0].clone(), keys[2].clone()];
        let visible = vec![keys[0].clone(), keys[2].clone(), key.clone()];
        let (fi, readout) = settle(&base, &moved);
        assert_eq!(readout, hidden);
        assert_eq!(removed_at(&fi, &key), Some(at(20)));
        // A touch stamped at the removal does not bring it back; a newer one does, onto `d2`.
        let with = |op: Op| [moved.to_vec(), vec![op]].concat();
        let (_, readout) = settle(&base, &with(Op::Touch(key.clone(), at(20))));
        assert_eq!(readout, hidden);
        let touched = with(Op::Touch(key.clone(), at(25)));
        let (fi, readout) = settle(&base, &touched);
        assert_eq!(readout, visible);
        assert_eq!(fi.get(2).unwrap().key, d2);
        // A removal newer than the touch takes it out again.
        let removed = [touched, vec![Op::Remove(key.clone(), at(30))]].concat();
        let (_, readout) = settle(&base, &removed);
        assert_eq!(readout, hidden);
    }

    /// A removal keeps the position register, so a removed moved element remembers where it was:
    /// an insert of that destination newer than the removal puts it back there.
    #[test]
    fn removal_keeps_the_pointer() {
        let (mut fi, keys) = virtual_index(3);
        let identity = keys[0].clone();
        let d = fi.create_keys(3, 1).next().unwrap(); // past the end
        fi.apply_move(&identity, d.clone(), at(10));
        assert_eq!(fi.remove_key_at(&d, at(20)), Some(identity.clone()));
        assert_eq!(identity_order(&fi), vec![keys[1].clone(), keys[2].clone()]);

        // Both records are in `moved` space and point at each other; either key finds the
        // identity's record.
        for key in [&identity, &d] {
            let Some((Slot::Moved(j), _)) = fi.resolve(key) else {
                panic!("{key:?} resolves outside `moved` space");
            };
            assert_eq!(fi.moved[j].key, identity);
            assert_eq!(fi.entry_by_key(key).map(|e| &e.key), Some(&identity));
        }
        assert_eq!(removed_at(&fi, &d), Some(at(20)));
        assert_eq!(fi.insert_key_at(d.clone(), at(30)), Some(2));
        assert_eq!(
            identity_order(&fi),
            vec![keys[1].clone(), keys[2].clone(), identity.clone()]
        );
        assert_eq!(fi.get(2).unwrap().key, d);
        // The removal stays on record after the revive.
        assert_eq!(removed_at(&fi, &identity), Some(at(20)));
    }

    /// A touch newer than the removal shows the element; an older or equal one does not, and a
    /// newer removal hides it again.
    #[test]
    fn touch_shows_a_removed_element() {
        let (mut fi, keys) = virtual_index(3);
        let key = &keys[1];
        let hidden = vec![keys[0].clone(), keys[2].clone()];
        fi.remove_key_at(key, at(10));
        assert!(!fi.touch(key, at(5)).0);
        assert!(!fi.touch(key, at(10)).0);
        assert_eq!(identity_order(&fi), hidden);

        assert!(fi.touch(key, at(15)).0);
        assert_eq!(identity_order(&fi), keys);
        assert_eq!(fi.get(1).unwrap().key, *key);
        assert!(!fi.touch(key, at(15)).0);

        assert_eq!(fi.remove_key_at(key, at(20)), Some(key.clone()));
        assert_eq!(identity_order(&fi), hidden);
        assert_eq!(removed_at(&fi, key), Some(at(20)));
    }

    /// `touched_at` is not encoded: a decoded index has none, and equals the original anyway.
    #[test]
    fn encode_drops_touched_at_and_keeps_removed_at() {
        let (mut fi, keys) = virtual_index(3);
        let d = fi.create_keys(3, 1).next().unwrap();
        fi.apply_move(&keys[0], d, at(10));
        fi.remove_key_at(&keys[0], at(20));
        fi.remove_key_at(&keys[1], at(20));
        fi.touch(&keys[1], at(30));
        fi.touch(&keys[2], at(40));

        let decoded = FractionalIndex::decode(&fi.encode().unwrap(), fi.suffix).unwrap();
        assert_eq!(decoded, fi);
        assert_eq!(identity_order(&decoded), identity_order(&fi));
        let all = |fi: &FractionalIndex| {
            fi.active
                .iter()
                .chain(&fi.moved)
                .cloned()
                .collect::<Vec<_>>()
        };
        assert!(all(&decoded).iter().all(|e| e.touched_at == Hlc::new(0)));
        for key in &keys {
            assert_eq!(removed_at(&decoded, key), removed_at(&fi, key));
        }
        assert_eq!(removed_at(&decoded, &keys[0]), Some(at(20)));
        assert_eq!(removed_at(&decoded, &keys[2]), None);
    }

    /// A removed element's records are the ones no key resolves to an active position through.
    #[test]
    fn removed_means_unreachable() {
        let (mut fi, keys) = virtual_index(3);
        let d = fi.create_keys(3, 1).next().unwrap();

        fi.apply_move(&keys[0], d.clone(), at(10));
        assert!(unreachable(&fi).is_empty(), "a move removes nothing");

        fi.remove_key_at(&keys[2], at(20));
        assert_eq!(unreachable(&fi), vec![keys[2].clone()]);

        // Removing a moved element strands its whole chain, identity record included.
        assert_eq!(fi.remove_key_at(&keys[0], at(30)), Some(keys[0].clone()));
        let mut stranded = unreachable(&fi);
        stranded.sort();
        let mut expected = vec![keys[0].clone(), keys[2].clone(), d.clone()];
        expected.sort();
        assert_eq!(stranded, expected);
        assert_eq!(identity_order(&fi), vec![keys[1].clone()]);

        // A revival makes the same records reachable again: an insert names the position it puts the
        // element on, so naming its identity brings it back onto that, not onto where it had moved.
        assert_eq!(fi.insert_key_at(keys[0].clone(), at(40)), Some(0));
        assert_eq!(unreachable(&fi), vec![keys[2].clone()]);
        assert_eq!(identity_order(&fi), vec![keys[0].clone(), keys[1].clone()]);
        assert_eq!(fi.get(0).unwrap().key, keys[0]);
        assert_eq!(fi.position_of(&d), Some(0)); // the position it passed through still finds it

        fi.insert_key_at(keys[2].clone(), at(50));
        assert!(unreachable(&fi).is_empty());
    }

    #[test]
    fn fractional_index() {
        let mut fi = FractionalIndex::default();

        let k2 = fi.create_key(0).unwrap().clone(); // [.]
        let k1 = fi.create_key(0).unwrap().clone(); // [. k2]
        let k4 = fi.create_key(2).unwrap().clone(); // [k1 k2 .]
        let k3 = fi.create_key(2).unwrap().clone(); // [k1 k2 . k4]

        let expected = vec![k1, k2, k3, k4];
        let mut actual: Vec<_> = fi.active.iter().map(|e| e.key.clone()).collect();
        assert_eq!(actual, expected);

        // entries should be already sorted
        actual.sort();
        assert_eq!(actual, expected);

        // every key is distinct => no dedups
        let keys: HashSet<_> = fi.active.iter().map(|e| e.key.clone()).collect();
        assert_eq!(keys.len(), fi.len());
    }

    #[test]
    fn fractional_indexes() {
        let mut fi = FractionalIndex::default();

        let k1 = fi.create_key(0).unwrap().clone(); // [.]
        let k2 = fi.create_key(1).unwrap().clone(); // [k1 .]

        let keys: Vec<_> = fi.create_keys(1, 2_000_000).collect();

        let mut last = &k1;
        for k in keys.iter() {
            assert!(k > last, "{k:?} should be higher than previous one");
            assert!(k < &k2, "{k:?} should be lower than the upper boundary");
            assert!(k.is_inline(), "{k:?} should be inlined");
            last = k;
        }
    }

    /// The integer model a run is planned against: how many positions of a given width sort strictly
    /// between two bounds.
    #[test]
    fn gap_capacity_counts_positions_at_each_width() {
        // A bounded gap holds 0x81..=0xbf at one digit, and 256x as many per digit added.
        assert_eq!(gap_capacity(&[0x80], &[0xc0], 1), 63);
        assert_eq!(gap_capacity(&[0x80], &[0xc0], 2), 16383);
        assert_eq!(gap_capacity(&[0x80], &[0xc0], 3), 4194303);
        // An unbounded one runs to the top of the width instead.
        assert_eq!(gap_capacity(&[0xe0], &[], 1), 31);
        assert_eq!(gap_capacity(&[0xe0], &[], 3), 0xff_ffff - 0xe0_0000);
        // Adjacent digits leave no room until a digit has been spent on the shared prefix.
        assert_eq!(gap_capacity(&[0x05, 0x03], &[0x05, 0x04], 2), 0);
        assert_eq!(gap_capacity(&[0x05, 0x03], &[0x05, 0x04], 3), 255);
        // A `hi` shorter than the width still bounds it, and `lo` extended by zeroes is excluded —
        // hence 0 rather than 1 at width 2.
        assert_eq!(gap_capacity(&[], &[0x00, 0x01], 2), 0);
        assert_eq!(gap_capacity(&[], &[0x00, 0x01], 3), 255);
        // Equal bounds (two sessions, one position) never open up, however wide the position gets.
        assert_eq!(
            gap_capacity(&[0x05], &[0x05], FractionalIndex::MAX_POSITION_LEN),
            0
        );
        // Nor do inverted ones.
        assert_eq!(gap_capacity(&[0x07], &[0x05], 4), 0);
    }

    /// A `move_to` relocates an element: it must appear at its new position and no longer be visible
    /// at its old one, and it must not be duplicated.
    #[test]
    fn move_to_relocates_element() {
        let mut fi = FractionalIndex::default();
        let a = fi.create_key(0).unwrap().clone(); // [A]
        let b = fi.create_key(1).unwrap().clone(); // [A B]
        let c = fi.create_key(2).unwrap().clone(); // [A B C]

        // Move B (at index 1) to the end.
        fi.move_to(1..2, 3);

        // New order is [A C B]: B is at the end...
        assert_eq!(identity_order(&fi), vec![a, c.clone(), b.clone()]);
        // ...its old position (index 1) is now C, so B is gone from there...
        assert_eq!(fi.get(1).unwrap().identity(), &c);
        // ...and B exists exactly once (no duplication) with the count unchanged.
        assert_eq!(fi.len(), 3);
        assert_eq!(fi.active.iter().filter(|e| e.identity() == &b).count(), 1);
        // It answers to the key it was minted as, not to the one the move gave it.
        assert_eq!(fi.position_of(&b), Some(2));
        assert_ne!(fi.get(2).unwrap().key, b);
    }

    /// A second move must not overwrite the identity the first one preserved.
    #[test]
    fn identity_survives_repeated_moves() {
        let mut fi = FractionalIndex::default();
        let a = fi.create_key(0).unwrap().clone(); // [A]
        let b = fi.create_key(1).unwrap().clone(); // [A B]
        let c = fi.create_key(2).unwrap().clone(); // [A B C]

        fi.move_to(1..2, 3); // [A C B]
        fi.move_to(2..3, 0); // [B A C]

        assert_eq!(identity_order(&fi), vec![b.clone(), a, c]);
        assert_eq!(fi.get(0).unwrap().identity(), &b);
        assert_ne!(fi.get(0).unwrap().key, b);
    }

    #[test]
    fn remove_drops_element() {
        let mut fi = FractionalIndex::default();
        let a = fi.create_key(0).unwrap().clone(); // [A]
        let b = fi.create_key(1).unwrap().clone(); // [A B]
        let c = fi.create_key(2).unwrap().clone(); // [A B C]

        // Remove an unmoved element from the middle: it answers to its own key.
        assert_eq!(fi.remove_key(&b), Some(b.clone()));
        assert_eq!(fi.len(), 2);
        assert_eq!(identity_order(&fi), vec![a.clone(), c.clone()]);
        // It is gone, and cannot be removed twice.
        assert_eq!(fi.position_of(&b), None);
        assert_eq!(fi.remove_key(&b), None);

        // Move C to the front, then remove it by its *identity* key (not its new position key).
        fi.move_to(1..2, 0); // view: [C A]
        assert_eq!(identity_order(&fi), vec![c.clone(), a.clone()]);
        assert_eq!(fi.remove_key(&c), Some(c.clone()));
        assert_eq!(fi.len(), 1);
        assert_eq!(identity_order(&fi), vec![a]);
        // Its move left nothing behind.
        assert_eq!(fi.position_of(&c), None);
    }

    #[test]
    fn concurrent_move_of_same_element_converges() {
        // Shared initial list [k0 k1 k2]; distinct session suffixes, so the peers never mint
        // colliding keys.
        let (mut a, keys) = virtual_index(3);
        let mut b = FractionalIndex::new(a.active.clone(), vec![], [b'b', 0, 0, 0]);
        let [k0, k1, k2] = [&keys[0], &keys[1], &keys[2]];

        // Both concurrently move k1: A to the end, B (newer) to the front.
        let da = a.create_keys(3, 1).next().unwrap();
        let db = b.create_keys(0, 1).next().unwrap();
        a.apply_move(k1, da.clone(), at(10));
        b.apply_move(k1, db.clone(), at(20));

        // Each replays the other's move.
        a.apply_move(k1, db, at(20));
        b.apply_move(k1, da, at(10));
        assert_eq!(a, b);
        let view_a: Vec<_> = a.view().collect();
        let view_b: Vec<_> = b.view().collect();
        assert_eq!(view_a, view_b, "peers must converge to the same view");
        assert_eq!(view_a, vec![k1, k0, k2]);
        // No duplication: element count is unchanged and k1 appears exactly once.
        assert_eq!(a.len(), 3, "moved element must not be duplicated on peer A");
        assert_eq!(b.len(), 3, "moved element must not be duplicated on peer B");
        assert_eq!(a.view().filter(|k| *k == k1).count(), 1);
    }

    #[test]
    fn encode_roundtrips_an_index_with_both_spaces_populated() {
        let suffix = [b'z', 1, 2, 3];
        let mut fi = FractionalIndex::new(vec![], vec![], suffix);
        let a = fi.create_key(0).unwrap().clone();
        let b = fi.create_key(1).unwrap().clone();
        let c = fi.create_key(2).unwrap().clone();
        let d = fi.create_key(3).unwrap().clone();

        fi.move_to(1..3, 4); // moves b and c, minting a destination for each
        fi.remove_key(&d); // tombstones d
        assert!(
            !fi.moved.is_empty(),
            "this test is only meaningful with a populated moved space"
        );

        let bytes = fi.encode().unwrap();
        let decoded = FractionalIndex::decode(&bytes, suffix).unwrap();
        assert_eq!(decoded, fi);
        // Canonical: re-encoding what we just read reproduces the same bytes.
        assert_eq!(decoded.encode().unwrap(), bytes);
        // Functionally identical, not just structurally equal.
        assert_eq!(
            decoded.view().collect::<Vec<_>>(),
            fi.view().collect::<Vec<_>>()
        );
        for key in [&a, &b, &c, &d] {
            assert_eq!(decoded.position_of(key), fi.position_of(key));
        }
    }

    /// The bitcode derive path, which is how an index reaches storage inside a `Worksheet`. The
    /// session suffix is not in the payload, so a decoded index comes back with a zeroed one.
    #[test]
    fn bitcode_derive_roundtrips() {
        let mut fi = FractionalIndex::new(vec![], vec![], [b'z', 1, 2, 3]);
        let a = fi.create_key(0).unwrap().clone();
        fi.create_key(1);
        fi.move_to(0..1, 2);

        let decoded: FractionalIndex = bitcode::decode(&bitcode::encode(&fi)).unwrap();
        assert_eq!(decoded.suffix, [0; 4]);
        assert_eq!(
            decoded.view().collect::<Vec<_>>(),
            fi.view().collect::<Vec<_>>()
        );
        assert_eq!(decoded.position_of(&a), fi.position_of(&a));
    }

    /// What the column layout is for: a sheet's worth of rows costs bytes, not kilobytes.
    #[test]
    fn a_sheet_sized_index_encodes_compactly() {
        let mut fi = FractionalIndex::new(vec![], vec![], [b'a', 0, 0, 0]);
        // A single bulk run, as an import or a large paste produces.
        let keys: Vec<_> = fi.create_keys(0, 10_000).collect();
        assert_eq!(keys.len(), 10_000);
        for (i, key) in keys.into_iter().enumerate() {
            fi.active
                .insert(i, Entry::new(key, PAST, FractionalKey::NULL));
        }

        let bytes = fi.encode().unwrap();
        assert!(
            bytes.len() < 64,
            "10k rows should encode in a few dozen bytes, got {}",
            bytes.len()
        );
        assert_eq!(FractionalIndex::decode(&bytes, fi.suffix).unwrap(), fi);
        // bitcode adds only its own framing on top.
        assert!(bitcode::serialize(&fi).unwrap().len() < 128);
    }

    #[test]
    fn insert_key_places_sorted_and_resurrects_only_forwards() {
        let mut fi = FractionalIndex::new(vec![], vec![], [b'a', 0, 0, 0]);
        let (v1, v2, v3) = (virtual_key(1), virtual_key(2), virtual_key(3));

        // Sorted placement, whatever order they arrive in.
        assert_eq!(fi.insert_key(v3.clone()), Some(0));
        assert_eq!(fi.insert_key(v1.clone()), Some(0));
        assert_eq!(fi.insert_key(v2.clone()), Some(1));
        assert_eq!(
            fi.view().cloned().collect::<Vec<_>>(),
            vec![v1, v2.clone(), v3]
        );

        // Idempotent: a key already active is not inserted twice.
        assert_eq!(fi.insert_key(v2.clone()), None);
        assert_eq!(fi.len(), 3);

        // A tombstone stands until an insert stamped past it undoes the delete.
        assert_eq!(fi.remove_key(&v2), Some(v2.clone()));
        assert_eq!(fi.insert_key_at(v2.clone(), PAST), None);
        assert_eq!(fi.len(), 2);
        assert_eq!(fi.insert_key(v2.clone()), Some(1));
        assert_eq!(fi.len(), 3);
    }

    #[test]
    fn virtual_keys_roundtrip_and_bracket_minted_ones() {
        for n in [1u32, 2, 7, 1_000, 1_048_576] {
            assert_eq!(virtual_ordinal(&virtual_key(n)), Some(n));
        }
        // Session-minted keys are not virtual.
        let mut fi = FractionalIndex::new(vec![], vec![], [b'a', 0, 0, 0]);
        fi.insert_key(virtual_key(1));
        fi.insert_key(virtual_key(2));
        let k = fi.create_keys(1, 1).next().unwrap();
        assert_eq!(virtual_ordinal(&k), None);
        // ...and they sort strictly inside the gap they were minted for.
        assert!(virtual_key(1) < k && k < virtual_key(2));
    }

    /// The watermark is derived state, so it has to come back with the bytes rather than in them.
    #[test]
    fn watermark_survives_a_roundtrip_and_a_tombstone() {
        let suffix = [b'a', 0, 0, 0];
        let mut fi = FractionalIndex::new(vec![], vec![], suffix);
        assert_eq!(fi.watermark(), 0);
        for n in 1..=3 {
            fi.insert_key(virtual_key(n));
        }
        assert_eq!(fi.watermark(), 3);

        let decoded = FractionalIndex::decode(&fi.encode().unwrap(), suffix).unwrap();
        assert_eq!(decoded.watermark(), 3);
        assert_eq!(decoded, fi);

        // Deleting a virtual row hands nothing back: its ordinal stays spent, so the next plan
        // starts above it and cannot run into the tombstone.
        fi.remove_key(&virtual_key(2));
        assert_eq!(fi.watermark(), 3);
        assert_eq!(fi.len(), 2);
        assert_eq!(fi.plan_virtual(3), vec![virtual_key(4)]);
        // The tombstone is still in `moved`, so the watermark is re-derivable from the two spaces.
        assert_eq!(
            FractionalIndex::decode(&fi.encode().unwrap(), suffix)
                .unwrap()
                .watermark(),
            3
        );
    }

    #[test]
    fn plan_virtual_extends_only_as_far_as_needed() {
        let mut fi = FractionalIndex::new(vec![], vec![], [b'a', 0, 0, 0]);
        assert_eq!(
            fi.plan_virtual(3),
            (1..=3).map(virtual_key).collect::<Vec<_>>()
        );
        for key in fi.plan_virtual(3) {
            fi.insert_key(key);
        }
        // Already long enough: nothing to mint.
        assert!(fi.plan_virtual(3).is_empty());
        assert!(fi.plan_virtual(0).is_empty());
        // Partially filled: only the ordinals past the watermark.
        assert_eq!(fi.plan_virtual(5), vec![virtual_key(4), virtual_key(5)]);
    }

    #[test]
    fn lower_bound_finds_the_insertion_point() {
        let mut fi = FractionalIndex::new(vec![], vec![], [b'a', 0, 0, 0]);
        assert_eq!(fi.active_index(&virtual_key(1)), 0);
        fi.insert_key(virtual_key(2));
        fi.insert_key(virtual_key(4));
        assert_eq!(fi.active_index(&virtual_key(1)), 0);
        assert_eq!(fi.active_index(&virtual_key(2)), 0); // present: its own slot
        assert_eq!(fi.active_index(&virtual_key(3)), 1);
        assert_eq!(fi.active_index(&virtual_key(5)), 2); // past the tail
    }

    /// Two peers moving one element mint a destination each: whichever order the two moves arrive
    /// in, the loser leaves the same record behind.
    #[test]
    fn concurrent_moves_apply_in_both_orders() {
        let (fi, keys) = virtual_index(3);
        let mut gen = fi.create_keys(3, 2);
        let (d1, d2) = (gen.next().unwrap(), gen.next().unwrap());
        drop(gen);
        let i = keys[0].clone();
        let (mut x, mut y) = (fi.clone(), fi);
        x.apply_move(&i, d1.clone(), at(10));
        x.apply_move(&i, d2.clone(), at(20));
        y.apply_move(&i, d2.clone(), at(20));
        y.apply_move(&i, d1.clone(), at(10));
        assert_eq!(x, y, "concurrent moves must commute");
        assert_eq!(x.position_of(&i), Some(2));
        assert_eq!(x.get(2).unwrap().key, d2);
        assert_eq!(x.position_of(&d1), Some(2));
    }
}
