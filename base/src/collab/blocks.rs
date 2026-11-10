use std::num::NonZeroUsize;
use std::{fmt, iter, slice};

use bitcode::__private::{Buffer, Decoder, Encoder, View};
use bitcode::{Decode, Encode};

use crate::collab::fractional_index::FractionalKey;

/// Entries a block holds at most.
const BLOCK_LEN: usize = 256;

/// A sorted map from `FractionalKey` kept in blocks of at most `BLOCK_LEN` entries. A position
/// (`At`) is two indices, valid until the next insert or remove.
#[derive(Clone)]
pub(crate) struct Blocks<V> {
    /// The first key of each block.
    firsts: Vec<FractionalKey>,
    /// Never empty; keys strictly increase across blocks.
    blocks: Vec<Block<V>>,
    len: usize,
}

#[derive(Clone)]
struct Block<V> {
    keys: Vec<FractionalKey>,
    vals: Vec<V>,
}

/// A block and a slot in it: an entry, or an insertion point.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct At {
    block: u32,
    slot: u32,
}

impl At {
    fn new(block: usize, slot: usize) -> Self {
        At {
            block: block as u32,
            slot: slot as u32,
        }
    }
}

impl<V> Default for Blocks<V> {
    fn default() -> Self {
        Blocks {
            firsts: Vec::new(),
            blocks: Vec::new(),
            len: 0,
        }
    }
}

impl<V> Blocks<V> {
    /// Fills blocks to `BLOCK_LEN`; an entry out of order is inserted, a repeated key replaces.
    pub(crate) fn from_sorted(entries: impl IntoIterator<Item = (FractionalKey, V)>) -> Self {
        let mut map = Self::default();
        for (key, val) in entries {
            let last = map.blocks.last().and_then(|block| block.keys.last());
            if last.is_some_and(|last| *last >= key) {
                map.insert(key, val);
            } else {
                map.insert_at(map.end(), key, val);
            }
        }
        map
    }

    pub(crate) fn len(&self) -> usize {
        self.len
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// `Err` is the insertion point.
    pub(crate) fn find(&self, key: &FractionalKey) -> Result<At, At> {
        let Some(block) = self
            .firsts
            .partition_point(|first| first <= key)
            .checked_sub(1)
        else {
            return Err(At::new(0, 0));
        };
        match self.blocks[block].keys.binary_search(key) {
            Ok(slot) => Ok(At::new(block, slot)),
            Err(slot) => Err(At::new(block, slot)),
        }
    }

    pub(crate) fn lookup(&self, key: &FractionalKey) -> Option<&V> {
        self.find(key).ok().map(|at| self.get(at))
    }

    pub(crate) fn key(&self, at: At) -> &FractionalKey {
        &self.blocks[at.block as usize].keys[at.slot as usize]
    }

    pub(crate) fn get(&self, at: At) -> &V {
        &self.blocks[at.block as usize].vals[at.slot as usize]
    }

    pub(crate) fn get_mut(&mut self, at: At) -> &mut V {
        &mut self.blocks[at.block as usize].vals[at.slot as usize]
    }

    /// The entry after the one at `at`.
    pub(crate) fn next(&self, at: At) -> Option<At> {
        let (block, slot) = (at.block as usize, at.slot as usize + 1);
        if slot < self.blocks[block].keys.len() {
            Some(At::new(block, slot))
        } else if block + 1 < self.blocks.len() {
            Some(At::new(block + 1, 0))
        } else {
            None
        }
    }

    /// The entry before `at`, an entry or an insertion point.
    pub(crate) fn prev(&self, at: At) -> Option<At> {
        if at.slot > 0 {
            Some(At::new(at.block as usize, at.slot as usize - 1))
        } else if at.block > 0 {
            let block = at.block as usize - 1;
            Some(At::new(block, self.blocks[block].keys.len() - 1))
        } else {
            None
        }
    }

    /// The insertion point past the last key.
    pub(crate) fn end(&self) -> At {
        let last = self.blocks.len().saturating_sub(1);
        At::new(
            last,
            self.blocks.get(last).map_or(0, |block| block.keys.len()),
        )
    }

    /// Returns the value it replaced.
    pub(crate) fn insert(&mut self, key: FractionalKey, val: V) -> Option<V> {
        match self.find(&key) {
            Ok(at) => Some(std::mem::replace(self.get_mut(at), val)),
            Err(at) => {
                self.insert_at(at, key, val);
                None
            }
        }
    }

    /// Inserts an absent `key` at its insertion point `at`; returns where it landed.
    pub(crate) fn insert_at(&mut self, at: At, key: FractionalKey, val: V) -> At {
        let (mut block, mut slot) = (at.block as usize, at.slot as usize);
        match self.blocks.get(block).map(|b| b.keys.len()) {
            None => return self.push_block(key, val),
            // Past the last key: a new block, so appends leave blocks full.
            Some(BLOCK_LEN) if slot == BLOCK_LEN && block + 1 == self.blocks.len() => {
                return self.push_block(key, val);
            }
            Some(BLOCK_LEN) => {
                let half = BLOCK_LEN / 2;
                let head = &mut self.blocks[block];
                let tail = Block {
                    keys: head.keys.split_off(half),
                    vals: head.vals.split_off(half),
                };
                self.firsts.insert(block + 1, tail.keys[0].clone());
                self.blocks.insert(block + 1, tail);
                if slot > half {
                    block += 1;
                    slot -= half;
                }
            }
            Some(_) => {}
        }
        self.len += 1;
        if slot == 0 {
            self.firsts[block] = key.clone();
        }
        let target = &mut self.blocks[block];
        target.keys.insert(slot, key);
        target.vals.insert(slot, val);
        At::new(block, slot)
    }

    fn push_block(&mut self, key: FractionalKey, val: V) -> At {
        self.len += 1;
        self.firsts.push(key.clone());
        self.blocks.push(Block {
            keys: vec![key],
            vals: vec![val],
        });
        At::new(self.blocks.len() - 1, 0)
    }

    pub(crate) fn remove(&mut self, key: &FractionalKey) -> Option<V> {
        let at = self.find(key).ok()?;
        Some(self.remove_at(at).1)
    }

    /// Removes the entry at `at`; an emptied block is dropped.
    pub(crate) fn remove_at(&mut self, at: At) -> (FractionalKey, V) {
        self.len -= 1;
        let (block, slot) = (at.block as usize, at.slot as usize);
        let target = &mut self.blocks[block];
        let entry = (target.keys.remove(slot), target.vals.remove(slot));
        if target.keys.is_empty() {
            self.blocks.remove(block);
            self.firsts.remove(block);
        } else if slot == 0 {
            self.firsts[block] = target.keys[0].clone();
        }
        entry
    }

    pub(crate) fn retain(&mut self, mut keep: impl FnMut(&FractionalKey, &mut V) -> bool) {
        for block in &mut self.blocks {
            retain_entries(&mut block.keys, &mut block.vals, &mut keep);
        }
        self.blocks.retain(|block| !block.keys.is_empty());
        self.firsts.clear();
        self.firsts
            .extend(self.blocks.iter().map(|block| block.keys[0].clone()));
        self.len = self.blocks.iter().map(|block| block.keys.len()).sum();
    }

    pub(crate) fn iter(&self) -> Iter<'_, V> {
        Iter {
            blocks: self.blocks.iter(),
            block: [].iter().zip([].iter()),
            remaining: self.len,
        }
    }

    pub(crate) fn into_entries(self) -> impl Iterator<Item = (FractionalKey, V)> {
        self.blocks
            .into_iter()
            .flat_map(|block| block.keys.into_iter().zip(block.vals))
    }
}

/// Keeps the entries of two parallel `Vec`s for which `keep` returns true, in order.
pub(crate) fn retain_entries<V>(
    keys: &mut Vec<FractionalKey>,
    vals: &mut Vec<V>,
    mut keep: impl FnMut(&FractionalKey, &mut V) -> bool,
) {
    let mut kept = 0;
    for i in 0..keys.len() {
        if keep(&keys[i], &mut vals[i]) {
            keys.swap(kept, i);
            vals.swap(kept, i);
            kept += 1;
        }
    }
    keys.truncate(kept);
    vals.truncate(kept);
}

/// The entries of a [`Blocks`], in key order.
pub struct Iter<'a, V> {
    blocks: slice::Iter<'a, Block<V>>,
    block: iter::Zip<slice::Iter<'a, FractionalKey>, slice::Iter<'a, V>>,
    remaining: usize,
}

impl<'a, V> Iterator for Iter<'a, V> {
    type Item = (&'a FractionalKey, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(entry) = self.block.next() {
                self.remaining -= 1;
                return Some(entry);
            }
            let block = self.blocks.next()?;
            self.block = block.keys.iter().zip(block.vals.iter());
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<V> ExactSizeIterator for Iter<'_, V> {}

/// By entries: the layout depends on insertion history.
impl<V: PartialEq> PartialEq for Blocks<V> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().eq(other.iter())
    }
}

impl<V: fmt::Debug> fmt::Debug for Blocks<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

/// By entries, so equal maps give equal bytes: a count, then all keys, then all values, read
/// straight from the blocks. Hand-written as bitcode has no public way to adapt a type.
pub struct BlocksEncoder<V: Encode> {
    counts: <usize as Encode>::Encoder,
    keys: <FractionalKey as Encode>::Encoder,
    vals: V::Encoder,
}

impl<V: Encode> Default for BlocksEncoder<V> {
    fn default() -> Self {
        BlocksEncoder {
            counts: Default::default(),
            keys: Default::default(),
            vals: Default::default(),
        }
    }
}

impl<V: Encode> Buffer for BlocksEncoder<V> {
    fn collect_into(&mut self, out: &mut Vec<u8>) {
        self.counts.collect_into(out);
        self.keys.collect_into(out);
        self.vals.collect_into(out);
    }

    fn reserve(&mut self, additional: NonZeroUsize) {
        self.counts.reserve(additional);
    }
}

impl<V: Encode> Encoder<Blocks<V>> for BlocksEncoder<V> {
    fn encode(&mut self, map: &Blocks<V>) {
        self.counts.encode(&map.len);
        let Some(len) = NonZeroUsize::new(map.len) else {
            return;
        };
        self.keys.reserve(len);
        self.vals.reserve(len);
        for block in &map.blocks {
            for key in &block.keys {
                self.keys.encode(key);
            }
            for val in &block.vals {
                self.vals.encode(val);
            }
        }
    }
}

impl<V: Encode> Encode for Blocks<V> {
    type Encoder = BlocksEncoder<V>;
}

pub struct BlocksDecoder<'a, V: Decode<'a>> {
    counts: <usize as Decode<'a>>::Decoder,
    keys: <FractionalKey as Decode<'a>>::Decoder,
    vals: V::Decoder,
}

impl<'a, V: Decode<'a>> Default for BlocksDecoder<'a, V> {
    fn default() -> Self {
        BlocksDecoder {
            counts: Default::default(),
            keys: Default::default(),
            vals: Default::default(),
        }
    }
}

impl<'a, V: Decode<'a>> View<'a> for BlocksDecoder<'a, V> {
    fn populate(&mut self, input: &mut &'a [u8], length: usize) -> bitcode::__private::Result<()> {
        // The keys and values to read are the sum of the counts: read those twice.
        let (mut counts, mut peek) = (<usize as Decode<'a>>::Decoder::default(), *input);
        counts.populate(&mut peek, length)?;
        let total = (0..length).fold(0usize, |total, _| {
            total.saturating_add(Decoder::<usize>::decode(&mut counts))
        });
        self.counts.populate(input, length)?;
        self.keys.populate(input, total)?;
        self.vals.populate(input, total)
    }
}

impl<'a, V: Decode<'a>> Decoder<'a, Blocks<V>> for BlocksDecoder<'a, V> {
    fn decode(&mut self) -> Blocks<V> {
        let len: usize = self.counts.decode();
        Blocks::from_sorted((0..len).map(|_| (self.keys.decode(), self.vals.decode())))
    }
}

impl<'a, V: Decode<'a>> Decode<'a> for Blocks<V> {
    type Decoder = BlocksDecoder<'a, V>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::collab::fractional_index::virtual_key;

    const N: u32 = BLOCK_LEN as u32;

    /// Asserts the invariants; returns the block lengths.
    fn layout<V>(map: &Blocks<V>) -> Vec<usize> {
        assert_eq!(map.firsts.len(), map.blocks.len());
        for (first, block) in map.firsts.iter().zip(&map.blocks) {
            assert!(!block.keys.is_empty() && block.keys.len() <= BLOCK_LEN);
            assert_eq!(block.keys.len(), block.vals.len());
            assert_eq!(first, &block.keys[0]);
        }
        let keys: Vec<_> = map.iter().map(|(key, _)| key).collect();
        assert!(keys.windows(2).all(|pair| pair[0] < pair[1]));
        assert_eq!(keys.len(), map.len());
        map.blocks.iter().map(|block| block.keys.len()).collect()
    }

    fn filled(keys: impl IntoIterator<Item = u32>) -> Blocks<u32> {
        let mut map = Blocks::default();
        for key in keys {
            assert_eq!(map.insert(virtual_key(key), key), None);
        }
        map
    }

    #[test]
    fn a_full_block_splits_in_half_unless_appended_to() {
        assert_eq!(layout(&filled(1..=N + 1)), vec![BLOCK_LEN, 1]);

        let mut map = filled((1..=N).map(|key| 2 * key));
        let at = map.find(&virtual_key(3)).unwrap_err();
        let at = map.insert_at(at, virtual_key(3), 3);
        assert_eq!((map.key(at), *map.get(at)), (&virtual_key(3), 3));
        assert_eq!(layout(&map), vec![BLOCK_LEN / 2 + 1, BLOCK_LEN / 2]);

        // Into the second half.
        let mut map = filled((1..=N).map(|key| 2 * key));
        let at = map.find(&virtual_key(N + 3)).unwrap_err();
        let at = map.insert_at(at, virtual_key(N + 3), 0);
        assert_eq!(map.key(at), &virtual_key(N + 3));
        assert_eq!(layout(&map), vec![BLOCK_LEN / 2, BLOCK_LEN / 2 + 1]);
    }

    #[test]
    fn firsts_follow_slot_zero_and_emptied_blocks_go() {
        let mut map = filled(1..=N + 2);
        map.insert(virtual_key(0), 0);
        assert_eq!(layout(&map), vec![BLOCK_LEN / 2 + 1, BLOCK_LEN / 2, 2]);
        assert_eq!(map.firsts[0], virtual_key(0));

        assert_eq!(map.remove(&virtual_key(N / 2 + 1)), Some(N / 2 + 1));
        assert_eq!(map.firsts[1], virtual_key(N / 2 + 2));
        assert_eq!(map.remove(&virtual_key(0)), Some(0));
        assert_eq!(map.firsts[0], virtual_key(1));
        assert_eq!(map.remove(&virtual_key(0)), None);

        map.remove(&virtual_key(N + 1));
        map.remove(&virtual_key(N + 2));
        assert_eq!(layout(&map), vec![BLOCK_LEN / 2, BLOCK_LEN / 2 - 1]);

        map.retain(|_, val| *val > N / 2);
        assert_eq!(layout(&map), vec![BLOCK_LEN / 2 - 1]);
        assert_eq!(map.firsts[0], virtual_key(N / 2 + 2));
    }

    #[test]
    fn next_and_prev_cross_block_boundaries() {
        let map = filled(1..=N + 1);
        let last_of_first = map.find(&virtual_key(N)).unwrap();
        let next = map.next(last_of_first).unwrap();
        assert_eq!(map.key(next), &virtual_key(N + 1));
        assert_eq!(map.next(next), None);
        assert_eq!(map.prev(next), Some(last_of_first));
        assert_eq!(map.prev(map.find(&virtual_key(1)).unwrap()), None);

        let mut walked = Vec::new();
        let mut at = map.find(&virtual_key(1)).ok();
        while let Some(here) = at {
            walked.push(*map.get(here));
            at = map.next(here);
        }
        assert_eq!(walked, (1..=N + 1).collect::<Vec<_>>());
    }

    #[test]
    fn equality_and_encoding_ignore_the_layout() {
        let appended = filled(1..=3 * N);
        let prepended = filled((1..=3 * N).rev());
        assert_ne!(layout(&appended), layout(&prepended));
        assert_eq!(appended, prepended);
        assert_eq!(bitcode::encode(&appended), bitcode::encode(&prepended));

        let decoded: Blocks<u32> = bitcode::decode(&bitcode::encode(&prepended)).unwrap();
        assert_eq!(decoded, appended);
        assert_eq!(layout(&decoded), vec![BLOCK_LEN; 3]);

        let mut changed = prepended.clone();
        changed.insert(virtual_key(1), 0);
        assert_ne!(changed, appended);
        assert_ne!(bitcode::encode(&changed), bitcode::encode(&appended));

        // Several maps in one payload, an empty one among them.
        let maps = vec![filled(1..=3), Blocks::default(), appended, filled([7])];
        let decoded: Vec<Blocks<u32>> = bitcode::decode(&bitcode::encode(&maps)).unwrap();
        assert_eq!(decoded, maps);
    }
}
