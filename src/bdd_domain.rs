use boolean_expression::*;

#[derive(Debug, PartialEq, Clone)]
pub struct BDDDomain {
    pub size: usize,
    pub binsize: usize,
    pub offset: usize, // where does the block start in the number of variables
    pub dom: BDDFunc,
}

impl BDDDomain {
    pub fn new(b: &mut BDD, size: usize, offset: usize) -> Self {
        let mut binsize = 1;
        let mut calcsize = 2;

        while calcsize < size {
            binsize += 1;
            calcsize *= 2;
        }

        let mut val = size - 1;
        let mut dom = BDD_ONE;

        for n in 0..binsize {
            let t = b.terminal(n + offset);
            let nt = b.not(t);
            let tmp = if val & 0x1 == 0x1 {
                b.or(nt, dom)
            } else {
                b.and(nt, dom)
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

    pub fn belongs(&self, terminal: BDDLabel) -> bool {
        terminal >= self.offset && terminal < self.offset + self.binsize
    }

    // check if domain accepts "d"
    pub fn digit(&self, b: &mut BDD, d: usize) -> BDDFunc {
        let mut val = d;
        let mut v = BDD_ONE;
        for n in 0..self.binsize {
            let term = if val & 0x1 == 0x1 {
                b.terminal(n + self.offset)
            } else {
                let t = b.terminal(n + self.offset);
                b.not(t)
            };
            v = b.and(term, v);
            val >>= 1;
        }
        v
    }

    pub fn allowed_values(&self, b: &mut BDD, f: BDDFunc) -> Vec<usize> {
        let mut res = Vec::new();
        for i in 0..self.size {
            let v = self.digit(b, i);
            // let v = b.and(v, d); // restrict to known values of the domain
            if b.and(f, v) != BDD_ZERO {
                res.push(i);
            }
        }
        res
    }

    pub fn domain_bdd(&self) -> BDDFunc {
        self.dom
    }

    pub fn equals(&self, other: &BDDDomain, b: &mut BDD) -> BDDFunc {
        if self.binsize != other.binsize {
            return BDD_ZERO;
        }

        let mut r = BDD_ONE;
        for n in 0..self.binsize {
            let at = b.terminal(n + self.offset);
            let bt = b.terminal(n + other.offset);
            let nat = b.not(at);
            let nbt = b.not(bt);

            let ab = b.and(at,bt);
            let nab = b.and(nat,nbt);
            let iff = b.or(ab, nab);

            r = b.and(r, iff);
        }
        r
    }
}


#[derive(Debug, PartialEq, Clone)]
pub struct BDDDomain2 {
    pub size: i32,
    pub binsize: i32,
    pub offset: i32, // where does the block start in the number of variables
    pub dom: buddy_rs::BDD,
}

impl BDDDomain2 {
    pub fn new(b: &buddy_rs::BDDManager, size: i32, offset: i32) -> Self {
        let mut binsize = 1;
        let mut calcsize = 2;

        while calcsize < size {
            binsize += 1;
            calcsize *= 2;
        }

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

        BDDDomain2 {
            size,
            binsize,
            offset,
            dom,
        }
    }

    pub fn belongs(&self, terminal: buddy_rs::BDDVar) -> bool {
        terminal >= self.offset && terminal < self.offset + self.binsize
    }

    // check if domain accepts "d"
    pub fn digit(&self, b: &buddy_rs::BDDManager, d: i32) -> buddy_rs::BDD {
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

    pub fn allowed_values(&self, b: &buddy_rs::BDDManager, f: &buddy_rs::BDD) -> Vec<i32> {
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

    pub fn domain_bdd(&self) -> buddy_rs::BDD {
        self.dom.clone()
    }

    pub fn equals(&self, other: &BDDDomain2, b: &buddy_rs::BDDManager) -> buddy_rs::BDD {
        if self.binsize != other.binsize {
            return b.zero();
        }

        let mut r = b.one();
        for n in 0..self.binsize {
            let at = b.ithvar(n + self.offset);
            let bt = b.ithvar(n + other.offset);
            let nat = b.not(&at);
            let nbt = b.not(&bt);

            let ab = b.and(&at,&bt);
            let nab = b.and(&nat,&nbt);
            let iff = b.or(&ab, &nab);

            r = b.and(&r, &iff);
        }
        r
    }
}


fn raw(bdd: &mut BDD, f: BDDFunc, d: &BDDDomain) {
    if f == BDD_ZERO {
        println!("input: ZERO");
    }
    else if f == BDD_ONE {
        println!("input: ONE");
    } else {
        println!("input: {:?}", f);
    }

    if f == BDD_ZERO || f == BDD_ONE {
        println!("done");
        return;
    }
    let node = bdd.nodes[f].clone();
    println!("node: {:?}", node);


    if node.label == d.offset {
        println!("node is starting the domain... {}", d.offset);
        let allowed = d.allowed_values(bdd, f);
        println!("variable can take on: {:?}", allowed);
        println!("skipping until variable {}", d.offset + d.binsize);
    }


    raw(bdd, node.lo, d);
    raw(bdd, node.hi, d);
}



#[test]
fn test_domain() {
    let domain: Vec<String> = vec![
        "l".into(),
        "u".into(),
        "unknown".into(),
        "unknown1".into(),
        "unknown2".into(),
    ];


    let mut b = BDD::new();
    let d = BDDDomain::new(&mut b, domain.len(), 5);

    let x = Expr::and(Expr::not(Expr::Terminal(5)), Expr::and(
         Expr::Terminal(6), Expr::not(Expr::Terminal(7))));

    let x = b.from_expr(&x);

    let allowed = d.allowed_values(&mut b, x);
    let allowed: Vec<_> = allowed.iter().map(|a| domain[*a].clone()).collect();

    assert!(allowed == vec!["unknown"]);
}
