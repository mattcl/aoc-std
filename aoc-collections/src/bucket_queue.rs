pub type DefaultBucketQueue<T> = BucketQueue<T, 64>;

#[derive(Debug, Clone)]
pub struct BucketQueue<T, const BS: usize> {
    buckets: Vec<Vec<T>>,
    first: Option<usize>,
}

impl<T, const BS: usize> Default for BucketQueue<T, BS> {
    fn default() -> Self {
        Self {
            buckets: Vec::default(),
            first: None,
        }
    }
}

impl<T, const BS: usize> BucketQueue<T, BS>
where
    T: Copy,
{
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, bucket: usize, value: T) {
        if bucket >= self.buckets.len() {
            self.buckets
                .resize_with(bucket + 1, || Vec::with_capacity(BS));
        }

        self.buckets[bucket].push(value);
        if self.first.filter(|f| *f <= bucket).is_none() {
            self.first = Some(bucket);
        }
    }

    pub fn pop(&mut self) -> Option<(usize, T)> {
        if let Some(min_bucket) = self.first {
            // This unwrap is safe because we shouldnot be here unless we set
            // first
            let value = self.buckets[min_bucket].pop().unwrap();

            if self.buckets[min_bucket].is_empty() {
                self.first =
                    ((min_bucket + 1)..self.buckets.len()).find(|v| !self.buckets[*v].is_empty());
            }

            Some((min_bucket, value))
        } else {
            None
        }
    }
}
