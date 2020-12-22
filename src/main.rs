use std::cell::RefCell;
use std::fmt;

const NU8: u8 = 8;
const NN: usize = (NU8 * NU8) as usize;
const STATE_COUNT: usize = NN * NN * NN * NN;

const MASK_COLS: [u64; 9] = [
    0,
    0x0101010101010101,
    0x0303030303030303,
    0x0707070707070707,
    0x0F0F0F0F0F0F0F0F,
    0x1F1F1F1F1F1F1F1F,
    0x3F3F3F3F3F3F3F3F,
    0x7F7F7F7F7F7F7F7F,
    0xFFFFFFFFFFFFFFFF,
];

fn mask_rect(x1: u8, x2: u8, y1: u8, y2: u8) -> u64 {
    assert!(x1 <= 8);
    assert!(x2 <= 8);
    assert!(y1 <= 8);
    assert!(y2 <= 8);
    if x1 == x2 || y1 == y2 {
        return 0;
    }
    assert!(x1 < x2);
    assert!(y1 < y2);
    let xs = if x2 == 8 {
        !MASK_COLS[x1 as usize]
    } else {
        MASK_COLS[(x2 - x1) as usize] << x1
    };
    if y2 - y1 == 8 {
        xs
    } else {
        (xs << (8 * (8 - (y2 - y1)))) >> (8 * (8 - y2))
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
struct RookRook {
    white_king: u8,
    white_rook: u8,
    black_king: u8,
    black_rook: u8,
}

impl RookRook {
    fn from(n: usize) -> Option<RookRook> {
        let white_king = n % NN;
        let n = (n - white_king) / NN;
        let white_rook = n % NN;
        let n = (n - white_rook) / NN;
        let black_king = n % NN;
        let n = (n - black_king) / NN;
        let black_rook = n % NN;
        let n = (n - black_rook) / NN;
        if n != 0 {
            return None;
        }
        Some(RookRook {
            white_king: white_king as u8,
            white_rook: if white_rook == white_king {
                64
            } else {
                white_rook as u8
            },
            black_king: black_king as u8,
            black_rook: if black_rook == white_king {
                64
            } else {
                black_rook as u8
            },
        })
    }
}

impl Into<usize> for RookRook {
    fn into(self) -> usize {
        assert!(self.white_king < 64);
        assert!(self.white_rook <= 64);
        assert!(self.black_king < 64);
        assert!(self.black_rook <= 64);
        let a = self.white_king as usize;
        let b = if self.white_rook == 64 {
            a
        } else {
            self.white_rook as usize
        };
        let c = self.black_king as usize;
        let d = if self.black_rook == 64 {
            a
        } else {
            self.black_rook as usize
        };
        (a) + NN * ((b) + NN * ((c) + NN * (d)))
    }
}

#[derive(Debug, Eq, PartialEq)]
enum Invalid {
    NotDistinctSquares,
    KingCheck,
}

#[derive(Debug, Eq, PartialEq, Clone)]
struct BitIterator(u64);

impl Iterator for BitIterator {
    type Item = u64;

    fn next(&mut self) -> Option<u64> {
        let v = self.0;
        if v == 0 {
            None
        } else {
            let r = v & (!v + 1);
            self.0 &= !r;
            Some(r)
        }
    }
}

#[derive(Debug, Clone)]
struct RookRookMoves {
    state: RookRook,
    white_rook_moves: BitIterator,
    white_king_moves: BitIterator,
}

impl Iterator for RookRookMoves {
    type Item = RookRook;

    fn next(&mut self) -> Option<RookRook> {
        if let Some(i) = self.white_rook_moves.next() {
            let black_rook = i.trailing_zeros() as u8;
            assert!(black_rook != self.state.white_rook);
            assert!(black_rook != self.state.white_king);
            assert!(black_rook != self.state.black_king);
            let white_rook = if self.state.black_rook == black_rook {
                64
            } else {
                self.state.black_rook
            };
            Some(RookRook {
                white_king: self.state.black_king,
                white_rook,
                black_king: self.state.white_king,
                black_rook,
            })
        } else if let Some(i) = self.white_king_moves.next() {
            let black_king = i.trailing_zeros() as u8;
            assert!(black_king != self.state.white_king);
            assert!(black_king != self.state.black_king);
            let white_rook = if black_king == self.state.black_rook {
                64
            } else {
                self.state.black_rook
            };
            Some(RookRook {
                white_king: self.state.black_king,
                white_rook,
                black_king,
                black_rook: self.state.white_rook,
            })
        } else {
            None
        }
    }
}

#[derive(Debug)]
enum ChessState {
    WhiteWin,
    Play(RookRookMoves),
}

impl ChessState {
    fn is_play(&self) -> bool {
        match self {
            ChessState::Play(_) => true,
            _ => false,
        }
    }

    fn play(self) -> Option<RookRookMoves> {
        match self {
            ChessState::Play(x) => Some(x),
            _ => None,
        }
    }
}

fn king_moves(king: u8) -> u64 {
    let kx = king % 8;
    let ky = king / 8;
    let king_mask = 1u64 << king;
    mask_rect(kx.max(1) - 1, kx.min(6) + 2, ky.max(1) - 1, ky.min(6) + 2) & !king_mask
}

fn rook_moves(rook: u8, pieces: &[u8]) -> u64 {
    if rook == 64 {
        return 0;
    }
    let rx = rook % 8;
    let ry = rook / 8;
    let mut rook_moves = (0xFFu64 << (8 * ry)) | (0x0101010101010101u64 << rx);
    for &o in pieces {
        if o == 64 {
            continue;
        }
        if rook_moves & (1u64 << o) == 0 {
            continue;
        }
        let sx = o % 8;
        let sy = o / 8;
        if sx < rx {
            rook_moves &= mask_rect(sx, 8, 0, 8);
            assert!(rook_moves & (1u64 << o) != 0);
        }
        if sx > rx {
            rook_moves &= mask_rect(0, sx + 1, 0, 8);
            assert!(rook_moves & (1u64 << o) != 0);
        }
        if sy < ry {
            rook_moves &= mask_rect(0, 8, sy, 8);
            assert!(rook_moves & (1u64 << o) != 0);
        }
        if sy > ry {
            rook_moves &= mask_rect(0, 8, 0, sy + 1);
            assert!(rook_moves & (1u64 << o) != 0);
        }
    }
    rook_moves & !(1u64 << rook)
}

impl RookRook {
    fn pieces_on_distinct_squares(&self) -> bool {
        // Kings must be on the board.
        // Rooks must be 64 or distinct from each other.
        self.white_king != self.black_king
            && self.white_king != self.white_rook
            && self.white_king != self.black_rook
            && self.black_king != self.white_rook
            && self.black_king != self.black_rook
            && (self.white_rook == 64
                || (self.white_rook != self.black_rook && self.white_rook < NU8 * NU8))
            && (self.black_rook == 64 || self.black_rook < NU8 * NU8)
            && self.white_king < NU8 * NU8
            && self.black_king < NU8 * NU8
    }

    fn state(&self) -> Result<ChessState, Invalid> {
        if !self.pieces_on_distinct_squares() {
            return Err(Invalid::NotDistinctSquares);
        }
        let white_rook = if self.white_rook == 64 {
            0
        } else {
            1u64 << self.white_rook
        };
        let white_king = 1u64 << self.white_king;
        let black_king = 1u64 << self.black_king;
        let white_rook_moves = rook_moves(
            self.white_rook,
            &[self.white_king, self.black_rook, self.black_king],
        );
        let white_king_moves = king_moves(self.white_king);
        if white_king_moves & black_king != 0 {
            return Err(Invalid::KingCheck);
        }
        if white_rook_moves & black_king != 0 {
            return Ok(ChessState::WhiteWin);
        }
        let white_king_moves = white_king_moves & !king_moves(self.black_king);
        Ok(ChessState::Play(RookRookMoves {
            state: self.clone(),
            white_rook_moves: BitIterator(white_rook_moves & !white_king),
            white_king_moves: BitIterator(white_king_moves & !white_rook),
        }))
    }
}

impl fmt::Debug for RookRook {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "RookRook {{ white_king: {}+8*{}, \
            white_rook: {}+8*{}, \
            black_king: {}+8*{}, \
            black_rook: {}+8*{} }}",
            self.white_king % 8,
            self.white_king / 8,
            self.white_rook % 8,
            self.white_rook / 8,
            self.black_king % 8,
            self.black_king / 8,
            self.black_rook % 8,
            self.black_rook / 8,
        )
    }
}

impl fmt::Display for RookRook {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for y in 0..(NU8 as usize) {
            if y > 0 {
                write!(f, "\n")?;
            }
            for x in 0..(NU8 as usize) {
                let i = y * (NU8 as usize) + x;
                if self.white_king as usize == i {
                    write!(f, "K")?;
                } else if self.white_rook as usize == i {
                    write!(f, "R")?;
                } else if self.black_king as usize == i {
                    write!(f, "k")?;
                } else if self.black_rook as usize == i {
                    write!(f, "r")?;
                } else if (x % 2) + (y % 2) == 1 {
                    write!(f, ",")?;
                } else {
                    write!(f, ".")?;
                }
            }
        }
        Ok(())
    }
}

fn main() {
    let flags = RefCell::new(vec![0u8; STATE_COUNT]);
    const VISITING: u8 = 1;
    const VISITED: u8 = 2;
    const WHITE_WIN: u8 = 4;
    const BLACK_WIN: u8 = 8;
    const INVALID: u8 = 16;
    const STALEMATE: u8 = 32;
    const TRIVIAL: u8 = 64;
    let stack = RefCell::new(Vec::<(usize, RookRookMoves)>::new());
    let visit_count = RefCell::new(0);

    let visit = |i: usize| {
        let s = RookRook::from(i).unwrap();
        let mut flags = flags.borrow_mut();
        if flags[i] & VISITING != 0 {
            return;
        }
        *visit_count.borrow_mut() += 1;
        flags[i] |= VISITING;
        match s.state() {
            Ok(ChessState::WhiteWin) => flags[i] |= VISITED | WHITE_WIN | TRIVIAL,
            Ok(ChessState::Play(moves)) => stack.borrow_mut().push((i, moves)),
            Err(_) => flags[i] |= VISITED | INVALID,
        }
    };

    for seed in 0..STATE_COUNT {
        if flags.borrow()[seed] != 0 {
            continue;
        }
        assert!(stack.borrow().is_empty());
        let n = *visit_count.borrow();
        visit(seed);
        loop {
            let (i, s) = {
                let mut stack_borrow = stack.borrow_mut();
                let (ref i, ref mut moves) = match stack_borrow.last_mut() {
                    Some(y) => y,
                    None => break,
                };
                (*i, moves.next())
            };
            if let Some(s) = s {
                visit(s.into());
                continue;
            }
            stack.borrow_mut().pop().unwrap();
            let mut flags = flags.borrow_mut();
            flags[i] |= VISITED;
            let moves = RookRook::from(i).unwrap().state().unwrap().play().unwrap();
            let mut all_black_win = true;
            let mut any_white_win = false;
            for s in moves {
                let j: usize = s.into();
                assert!(j != i);
                let f = flags[j];
                assert!(f & VISITING != 0);
                if f & INVALID != 0 {
                    assert!(
                        RookRook::from(j).unwrap().state().err()
                            != Some(Invalid::NotDistinctSquares)
                    );
                    continue;
                }
                assert!(f & INVALID == 0);
                if f & BLACK_WIN != 0 {
                    any_white_win = true;
                }
                if f & WHITE_WIN == 0 {
                    all_black_win = false;
                }
            }
            if any_white_win {
                flags[i] |= WHITE_WIN;
            } else if all_black_win {
                flags[i] |= BLACK_WIN;
            } else {
                flags[i] |= STALEMATE;
            }
        }
        let n = *visit_count.borrow() - n;
        if n != 1 {
            println!(
                "Visited {} states starting from\n{}",
                n,
                RookRook::from(seed).unwrap()
            );
        }
    }
    let flags = flags.borrow();
    for i in 0..STATE_COUNT {
        if flags[i] & (INVALID | TRIVIAL) != 0 {
            continue;
        }
        let s = RookRook::from(i).unwrap();
        if flags[i] & WHITE_WIN != 0 {
            println!("WHITE_WIN {:02x}:\n{}", flags[i], s);
        } else if flags[i] & BLACK_WIN != 0 {
            println!("BLACK_WIN {:02x}:\n{}", flags[i], s);
        } else {
            assert!(flags[i] & STALEMATE != 0);
            println!("STALEMATE {:02x}:\n{}", flags[i], s);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test1() {
        assert_eq!(king_moves(7), (1 << 6) | (1 << 14) | (1 << 15));
        assert_eq!(
            king_moves(15),
            (1 << 23) | (1 << 22) | (1 << 14) | (1 << 7) | (1 << 6)
        );
        assert_eq!(king_moves(0), (1 << 1) | (1 << 8) | (1 << 9));
        assert_eq!(
            king_moves(8),
            (1 << 0) | (1 << 1) | (1 << 9) | (1 << 16) | (1 << 17)
        );
        assert_eq!(
            RookRook::from(16747952).unwrap().state().err(),
            Some(Invalid::KingCheck)
        );
        assert!(king_moves(0) & 2 != 0);
        assert_eq!(
            RookRook {
                white_king: 0,
                black_king: 1,
                white_rook: 2,
                black_rook: 64
            }
            .state()
            .err(),
            Some(Invalid::KingCheck)
        );
    }

    #[test]
    fn test_iterator() {
        assert_eq!(
            BitIterator(0x111u64).collect::<Vec<_>>(),
            vec![0x1, 0x10, 0x100]
        );
    }

    fn test_mask(x1: u8, x2: u8, y1: u8, y2: u8) -> Option<(u8, u8)> {
        let m = mask_rect(x1, x2, y1, y2);
        for y in 0..8 {
            for x in 0..8 {
                let i = 8 * y + x;
                let r = m & (1u64 << i) != 0;
                let e = y1 <= y && y < y2 && x1 <= x && x < x2;
                if e != r {
                    return Some((x, y));
                }
            }
        }
        None
    }

    #[test]
    fn test_mask_1() {
        assert_eq!(test_mask(0, 8, 3, 8), None);
        assert_eq!(test_mask(0, 8, 0, 5), None);
        assert_eq!(test_mask(0, 5, 0, 8), None);
        assert_eq!(test_mask(3, 8, 0, 8), None);
    }

    #[test]
    fn test_rook_blocks_check() {
        let black_king = 0;
        let black_rook = 1;
        let white_rook = 2;
        let white_king = 3;
        let s = RookRook {
            white_king,
            white_rook,
            black_king,
            black_rook,
        };
        assert!(s.state().unwrap().is_play());
    }

    #[test]
    fn test_king_moves() {
        assert_eq!(king_moves(0), 0x302);
    }
}
