use buddy_rs::*;

#[derive(Debug, PartialEq, Clone)]
pub struct BDDDomain {
    pub size: i32,
    pub binsize: i32,
    pub offset: i32, // where does the block start in the number of variables
    pub dom: BDD,
}

impl BDDDomain {
    pub fn compute_binsize(size: i32) -> i32 {
        let mut binsize = 1;
        let mut calcsize = 2;

        while calcsize < size {
            binsize += 1;
            calcsize *= 2;
        }
        binsize
    }

    pub fn new(b: &BDDManager, size: i32, offset: i32) -> Self {
        let binsize = Self::compute_binsize(size);

        let mut val = size - 1;
        let mut dom = b.one();

        for n in 0..binsize {
            let t = b.ithvar(n + offset);
            let nt = b.not(&t);
            let tmp = if val & 0x1 == 0x1 {
                b.or(&nt, &dom)
            } else {
                b.and(&nt, &dom)
            };

            val >>= 1;
            dom = tmp;
        }

        BDDDomain {
            size,
            binsize,
            offset,
            dom,
        }
    }

    pub fn belongs(&self, terminal: BDDVar) -> bool {
        terminal >= self.offset && terminal < self.offset + self.binsize
    }

    // check if domain accepts "d"
    pub fn digit(&self, b: &BDDManager, d: i32) -> BDD {
        let mut val = d;
        let mut v = b.one();
        for n in 0..self.binsize {
            let term = if val & 0x1 == 0x1 {
                b.ithvar(n + self.offset)
            } else {
                let t = b.ithvar(n + self.offset);
                b.not(&t)
            };
            v = b.and(&term, &v);
            val >>= 1;
        }
        v
    }

    pub fn allowed_values(&self, b: &BDDManager, f: &BDD) -> Vec<i32> {
        let mut res = Vec::new();
        for i in 0..self.size {
            let v = self.digit(b, i);
            // let v = b.and(v, d); // restrict to known values of the domain
            if b.and(&f, &v) != b.zero() {
                res.push(i);
            }
        }
        res
    }

    pub fn domain_bdd(&self) -> BDD {
        self.dom.clone()
    }

    pub fn equals(&self, b: &BDDManager, other: &BDDDomain) -> BDD {
        if self.binsize != other.binsize {
            return b.zero();
        }

        let mut r = b.one();
        for n in 0..self.binsize {
            let at = b.ithvar(n + self.offset);
            let bt = b.ithvar(n + other.offset);
            let iff = b.biimp(&at, &bt);
            r = b.and(&r, &iff);
        }
        r
    }
}
