//! Storage and headers for long clauses.
use crate::{
    clause_arena::{ClauseArena, ClauseHeader, HeaderWord},
    lit::LitIdx,
    util::transparent::Transparent,
};

const REDUNDANT_BIT: u32 = 0;
const PROTECTED_BIT: u32 = REDUNDANT_BIT + 1;

const GLUE_START: u32 = PROTECTED_BIT + 1;
const GLUE_WIDTH: u32 = 6;
const USED_START: u32 = GLUE_START + GLUE_WIDTH;
const USED_WIDTH: u32 = 2;

/// Header of a long clause.
#[derive(Clone, Copy, Default, Transparent)]
#[repr(transparent)]
pub struct LongHeader {
    words: [HeaderWord; 2],
}

/// Storage for long clauses.
pub type LongClauses = ClauseArena<LongHeader>;

pub use crate::clause_arena::ClauseRef;

impl ClauseHeader for LongHeader {
    fn shrink_clause(&mut self, _old_len: usize, new_len: usize) {
        if self.search_pos() >= new_len {
            self.set_search_pos(0)
        }
    }
}

impl LongHeader {
    /// Returns new clause data for an input clause.
    pub fn new_input_clause() -> Self {
        Self::default()
    }

    /// Returns new clause data for a learned clause.
    pub fn new_learned_clause() -> Self {
        let mut data = Self::default();
        data.set_redundant(true);
        // Count the initial learning as use, so that the clause can survive an immediately
        // following reduction.
        data.set_used(1);
        data
    }

    /// Returns whether the clause is redundant.
    pub fn redundant(&self) -> bool {
        self.words[0].bit::<REDUNDANT_BIT>()
    }

    /// Sets whether the clause is redundant.
    pub fn set_redundant(&mut self, redundant: bool) {
        self.words[0].set_bit::<REDUNDANT_BIT>(redundant)
    }

    /// Returns whether the clause is protected.
    pub fn protected(&self) -> bool {
        self.words[0].bit::<PROTECTED_BIT>()
    }

    /// Sets whether the clause is protected.
    pub fn set_protected(&mut self, protected: bool) {
        self.words[0].set_bit::<PROTECTED_BIT>(protected)
    }

    /// Returns the glue level of the clause.
    ///
    /// Also called Literal Block Distance (LBD).
    pub fn glue(&self) -> usize {
        self.words[0].field::<GLUE_START, GLUE_WIDTH>() as usize
    }

    /// Sets the glue level of the clause.
    ///
    /// Also called Literal Block Distance (LBD).
    pub fn set_glue(&mut self, glue: usize) {
        self.words[0].set_field::<GLUE_START, GLUE_WIDTH>(glue as u32)
    }

    /// Returns how often the clause was recently used.
    ///
    /// This is incremented everytime the clause is involved in a conflict and decremented
    /// during every reduction. Both increments and decrements are saturating.
    pub fn used(&self) -> usize {
        self.words[0].field::<USED_START, USED_WIDTH>() as usize
    }

    /// Sets how often the clause was recently used.
    ///
    /// This is incremented everytime the clause is involved in a conflict and decremented
    /// during every reduction. Both increments and decrements are saturating.
    pub fn set_used(&mut self, used: usize) {
        self.words[0].set_field::<USED_START, USED_WIDTH>(used as u32)
    }

    /// Returns the circular scanning position used durig propagation.
    ///
    /// Note that this starts counting with position 0 for the 3rd literal, i.e. skipping the
    /// watched literals.
    ///
    /// See also ["Optimal Implementation of Watched Literals and More General
    /// Techniques"](https://doi.org/10.1613/jair.4016)
    pub fn search_pos(&self) -> usize {
        LitIdx::from(self.words[1]) as usize
    }

    /// Updates the circular scanning position used durig propagation.
    ///
    /// Note that this starts counting with position 0 for the 3rd literal, i.e. skipping the
    /// watched literals.
    pub fn set_search_pos(&mut self, pos: usize) {
        self.words[1] = HeaderWord::new(pos as LitIdx)
    }
}
