use std::collections::{HashMap, HashSet};
use std::ops::Range;

use itertools::Itertools;
use rangemap::RangeMap;

#[derive(Default, Debug)]
pub struct SparseVec<T> {
    map: RangeMap<u64, usize>,
    data: HashMap<usize, (Range<u64>, Vec<T>)>,
    key_counter: usize,
}

impl<T: Copy> SparseVec<T> {
    fn assert_invariants(&self) {
        for (range, key) in self.map.iter() {
            let (old_range, vec) = &self.data[key];
            assert_eq!(range, old_range);
            assert_eq!(vec.len(), (range.end - range.start) as usize);
        }
        let mut duplicates = HashMap::new();
        for (range, key) in self.map.iter() {
            if let Some(other) = duplicates.get(key) {
                panic!("{range:?} and {other:?} use key {key}");
            } else {
                duplicates.insert(*key, range.clone());
            }
        }
    }

    fn resize_block(
        data: &mut HashMap<usize, (Range<u64>, Vec<T>)>,
        key: &usize,
        range: &Range<u64>,
    ) {
        let (old_range, vec) = data.get_mut(key).unwrap();
        let new_vec_range: Range<usize> = cast_range(sub_range(range, old_range.start));
        if new_vec_range.start != 0 {
            vec.copy_within(new_vec_range.clone(), 0);
        }
        vec.truncate(new_vec_range.end - new_vec_range.start);
        *old_range = range.clone();
    }

    fn collect_garbage(&mut self) {
        let mut used = HashSet::with_capacity(self.map.len());
        used.extend(self.map.iter().map(|(_, k)| *k));
        self.data.retain(|k, _| used.contains(k));
    }

    pub fn get(&self, range: Range<u64>) -> Option<&[T]> {
        let (found_range, key) = self.map.get_key_value(&range.start)?;
        let slice_range = sub_range(&range, found_range.start);
        self.data[key].1.get(cast_range(slice_range))
    }

    pub fn get_mut(&mut self, range: Range<u64>) -> Option<&mut [T]> {
        let (found_range, key) = self.map.get_key_value(&range.start)?;
        let slice_range = sub_range(&range, found_range.start);
        self.data
            .get_mut(key)
            .unwrap()
            .1
            .get_mut(cast_range(slice_range))
    }

    pub fn overlaps(&self, range: &Range<u64>) -> bool {
        self.map.overlaps(range)
    }

    pub fn insert(&mut self, data: Vec<T>, addr: u64) {
        if data.is_empty() {
            return;
        }

        let insert_range = addr..addr + data.len() as u64;

        let start_key = self.map.get(&insert_range.start);
        // Will create duplicate key
        if let Some(&key) = start_key {
            if start_key == self.map.get(&insert_range.end) {
                let (range, vec) = self.data.get(&key).unwrap();
                let range = range.clone();
                let lower_range = range.start..insert_range.start;
                let upper_range = insert_range.end..range.end;

                if !upper_range.is_empty() {
                    self.map.insert(upper_range.clone(), self.key_counter);
                    let copy_range = sub_range(&upper_range, range.start);
                    self.data.insert(
                        self.key_counter,
                        (upper_range, vec[cast_range(copy_range)].to_vec()),
                    );
                    self.key_counter += 1;
                }

                if !lower_range.is_empty() {
                    Self::resize_block(&mut self.data, &key, &lower_range);
                    self.map.insert(lower_range, key);
                }
            }
        }

        // Insert
        self.map.insert(insert_range.clone(), self.key_counter);
        self.data.insert(self.key_counter, (insert_range, data));
        self.key_counter += 1;

        // Resize
        for (range, key) in self.map.iter() {
            Self::resize_block(&mut self.data, key, range);
        }

        // Merge
        loop {
            let mut mergable = None;
            for ((range, _), (range2, _)) in self.map.iter().tuple_windows() {
                if range.end == range2.start {
                    mergable = Some((range.clone(), range2.clone()));
                    break;
                }
            }

            if let Some((range, range2)) = mergable {
                let key1 = *self.map.get(&range.start).unwrap();
                let key2 = *self.map.get(&range2.start).unwrap();

                let (_, vec2) = self.data.remove(&key2).unwrap();
                self.map.remove(range2.clone());
                let (data_range, vec1) = self.data.get_mut(&key1).unwrap();
                *data_range = range.start..range2.end;
                vec1.extend_from_slice(&vec2);
                self.map.insert(data_range.clone(), key1);
            } else {
                break;
            }
        }

        self.collect_garbage();

        #[cfg(debug_assertions)]
        self.assert_invariants();
    }

    pub fn ranges(&self) -> impl Iterator<Item = Range<u64>> + '_ {
        self.map.iter().map(|(range, _)| range.clone())
    }

    pub fn stored_len(&self) -> usize {
        self.map.iter().map(|(_, k)| self.data[k].1.len()).sum()
    }
}

fn sub_range(range: &Range<u64>, offset: u64) -> Range<u64> {
    range.start - offset..range.end - offset
}

fn cast_range<I, O: TryFrom<I>>(range: Range<I>) -> Range<O>
where
    O::Error: std::fmt::Debug,
{
    range.start.try_into().unwrap()..range.end.try_into().unwrap()
}

#[test]
fn sparsevec() {
    let mut map = SparseVec::default();
    let mut insert_test = |n: u8, size: usize, addr: u64| {
        map.insert(vec![n; size], addr);
        map.assert_invariants();
        assert_eq!(map.get(addr..addr + size as u64).unwrap(), &vec![n; size]);
    };

    insert_test(1, 20, 0);
    insert_test(2, 10, 20);
    insert_test(3, 10, 15);
    insert_test(4, 5, 5);
}

#[test]
fn sparsevec_fuzz() {
    use rand::{Rng, SeedableRng};

    let mut map = SparseVec::default();
    let mut insert_test = |n: u8, size: usize, addr: u64| {
        let vec = Vec::from_iter((0..size).map(|v| (v as u8).overflowing_mul(n).0));
        map.insert(vec.clone(), addr);
        map.assert_invariants();
        assert_eq!(map.get(addr..addr + size as u64).unwrap(), &vec);
    };

    let mut rng = rand::rngs::StdRng::seed_from_u64(0);
    for _ in 0..1_000_000 {
        let n = rng.gen_range(0..255);
        let size = rng.gen_range(0..1000);
        let addr = rng.gen_range(0..1000);
        insert_test(n, size, addr);
    }
}

#[test]
fn sparsevec_u64_fuzz() {
    use rand::{Rng, SeedableRng};

    let mut map = SparseVec::default();
    let mut insert_test = |n: u64, size: usize, addr: u64| {
        let vec = Vec::from_iter((0..size).map(|v| (v as u64).overflowing_mul(n).0));
        map.insert(vec.clone(), addr);
        map.assert_invariants();
        assert_eq!(map.get(addr..addr + size as u64).unwrap(), &vec);
    };

    let mut rng = rand::rngs::StdRng::seed_from_u64(0);
    for _ in 0..1_000_000 {
        let n = rng.gen_range(0..255);
        let size = rng.gen_range(0..1000);
        let addr = rng.gen_range(0..1000);
        insert_test(n, size, addr);
    }
}
