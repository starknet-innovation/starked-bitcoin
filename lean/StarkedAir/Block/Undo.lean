/-
**Undo bytes (M3a.6 `BLK-COMMIT`, D-038).** The spent-output records as one byte per row, the byte
table's AIR (`Block/Bytes.lean`) with its length read from public input 8 instead of 0 and its own
relation `REL_UBYTE`. M3a hashes these bytes without checking their content (D-029).
-/
import StarkedAir.Block.Bytes

namespace StarkedAir

/-- Replace public-input indices. -/
def Expr.mapPub (f : ℕ → ℕ) : Expr → Expr
  | .col t i off => .col t i off
  | .const v => .const v
  | .add a b => .add (a.mapPub f) (b.mapPub f)
  | .sub a b => .sub (a.mapPub f) (b.mapPub f)
  | .mul a b => .mul (a.mapPub f) (b.mapPub f)
  | .neg a => .neg (a.mapPub f)
  | .pub i => .pub (f i)

theorem Expr.eval_mapPub (f : ℕ → ℕ) (n : ℕ) (pc : List PreCol) (pub : ℕ → F) (main : ℕ → ℕ → F) (r : ℕ) :
    ∀ e : Expr, (e.mapPub f).eval n pc pub main r = e.eval n pc (pub ∘ f) main r
  | .col t i off => by cases t <;> rfl
  | .const v => rfl
  | .add a b => by simp [Expr.mapPub, Expr.eval, Expr.eval_mapPub f n pc pub main r a, Expr.eval_mapPub f n pc pub main r b]
  | .sub a b => by simp [Expr.mapPub, Expr.eval, Expr.eval_mapPub f n pc pub main r a, Expr.eval_mapPub f n pc pub main r b]
  | .mul a b => by simp [Expr.mapPub, Expr.eval, Expr.eval_mapPub f n pc pub main r a, Expr.eval_mapPub f n pc pub main r b]
  | .neg a => by simp [Expr.mapPub, Expr.eval, Expr.eval_mapPub f n pc pub main r a]
  | .pub i => rfl

end StarkedAir

namespace StarkedAir.Block.Undo

open StarkedAir
open StarkedAir.Sha256 (col)

def REL_UBYTE : ℕ := 17
/-- The undo record's length is public input 8. -/
def PUB_LEN : ℕ := 8

def remap (i : ℕ) : ℕ := if i = 0 then PUB_LEN else i

def constraints : List Expr := Block.constraints.map (Expr.mapPub remap)

def undo : Comp where
  air := { name := "block_undo", nMain := 12, pre := Block.preCols, constraints := constraints }
  lookups := [⟨REL_UBYTE, .mul (col Block.ACTIVE) (col Block.MULT), [col Block.POS, col Block.BYTE]⟩]

/-- **A satisfied undo table is a satisfied byte table** for the public inputs with `pub 0 := pub 8`. -/
theorem bytes_sat {n : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F}
    (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n Block.preCols pub main r = 0) :
    ∀ r < n, ∀ c ∈ Block.constraints, c.eval n Block.preCols (pub ∘ remap) main r = 0 := by
  intro r hr c hc
  rw [← Expr.eval_mapPub]
  exact hsat r hr _ (List.mem_map.mpr ⟨c, hc, rfl⟩)

end StarkedAir.Block.Undo
