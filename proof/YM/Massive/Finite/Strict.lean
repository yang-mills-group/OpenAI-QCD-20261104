import YM.Massive.Finite.Checker

/-!
# Lower pressure bound at the *actual* cutoff for unequal masses

`Z ≥ Z_gauge × ∏_{i:Flavor F} (4+m_i)^(12*n^4)`. Does not pay a factorial
in volume or require positivity on each fixed gauge configuration; works for
negative bare masses, arbitrary F. In particular, entirely removes a condition of
paired masses in proving strict partition function positivity in this regime.

Proof: on the bipartite lattice saturating all spin letters on one color
means every remaining spin term is onsite, giving the stated ubiquitous factor
for sites of the other color; and saturating *every* site leaves the
unquenched joint expectation reduced to the pure gauge integral. Copies are
with the correct graded order reversals for reflection in the project conventions.
So apply raw chessboard to those saturations to get the bound.

The inequality is for the starting normalization; it's not enough to say what
can propagate with which estimates through RG. In particular, after blocking
*and extracting new scalar factors* one may need pressure bounds exponential
in **coarse rather than fine** volume, not settled by this argument.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Checker
open QCD QCD.Lat QCD.Grass QCD.RP Lattice Wilson MeasureTheory Function Finset
open Onsite Chess
open scoped BigOperators Topology Matrix.Norms.Frobenius ComplexOrder
variable {n l : Side} {F : ℕ} (X : Support n) (R : Regulator n F)

lemma fill_empty : fill (∅ : Support n) F=1:=by
  ext1 U; change vol _ = 1; simp [modes]
lemma fill_join {i : Site n} (h : i∉X) : fill ({i} : Support n) F * fill X F=fill (insert i X) F := by
  ext1 U; change vol _*vol _=vol _
  have hh : modes ({i} : Support n) F ∪ modes X F=modes (insert i X) F:=by ext; simp
  have hd : Disjoint (modes ({i} : Support n) F) (modes X F):=by
    apply disjoint_left.mpr; simp; intro a b; exact h b
  rw [← pair_union _ _ hd, hh]

def tile (F : ℕ) (b : Bool) (i : Site n) : Insertion n F := if b then fill ({i} : Support n) F else 1

variable (he : n.val=2*l.val)
local notation "Tʳ" => tiling he

lemma pattern : Chess.Pattern R (tiling he) (tile F) := by
  constructor
  · rintro (_|_) i
    · exact flooring_one
    exact floors_fill ({(i : Site n)} : Support n) F (by simpa using belongs he i)
  · rintro (_|_) i
    · exact invariant_one
    exact fill_invariant ({(i : Site n)} : Support n)
  · rintro (_|_) i
    · exact ⟨false, fun _ => map_one grade⟩
    exact ⟨false, fun U => Onsite.top ({(i : Site n)} : Support n) U⟩
  rintro p a (_|_) v
  · apply Or.inl; exact pic_one
  apply Or.inl
  unfold tile
  rw [if_pos rfl,if_pos rfl,reflected_fill,mirror he]; simp [opposite]

lemma deployed (C : List (Site n)) (h : C.Nodup) (g : Site n → Bool) :
    Chess.Array.use (tiling he) C (tile F) g = fill (C.toFinset.filter (fun i => g i)) F := by
  induction C with
  | nil => exact fill_empty.symm
  | cons a l ih =>
    obtain ⟨hh,H⟩ := List.nodup_cons.mp h
    rw [List.toFinset_cons, filter_insert]
    change tile F (g a) a * Chess.Array.use (tiling he) _ _ _= _
    rw [ih H]; cases hg : g a
    · simp [tile]
    simpa [hg,tile] using fill_join (F:=F) (l.toFinset.filter fun i => g i) (i:=a) (by simp [hh])

open Chess.Array

def selector (X : Support n) (i : Site n) : Bool := decide (i∈X)

lemma occupied_cost : cost (T:=tiling he) (selector X) (tile F) R = ‖R.raw (fill X F)‖:=by
    have h : ((univ:Finset (Site n)).toList.toFinset.filter fun i => selector X i)=X:=by ext; simp [selector]
    unfold cost; rw [deployed he (F:=F) (h:=nodup_toList _) univ.toList (selector X),h]

lemma reading (h : Covers X) : cost (T:=tiling he) (selector X) (tile F) R= Wilson.partition su n R.β * volumeMass R ^ (Xᶜ).card := by
    have hu := partition_pos (G:=su) (n:=n) R.β
    rw [occupied_cost,expectation X R h,Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hu.le (pow_nonneg (volumeMass_nonneg R) _))]

lemma all_filled : cost (T:=tiling he) (fun _ => true) (tile F) R = Wilson.partition su n R.β:=by
  have he' := reading (univ : Support n) R he (fun _ _ _=>⟨mem_univ _,mem_univ _⟩)
  rw [show selector (univ:Support n)=(fun _ => true) from funext fun _ => by simp [selector]] at he'
  simpa using he'

lemma blank : cost (T:=tiling he) (fun _ => false) (tile F) R = ‖R.Z‖:=by
  have he' := occupied_cost (∅ : Support n) R he
  rw [show selector (∅:Support n)=(fun _ => false) from funext fun _ => by simp [selector], fill_empty] at he'; exact he'

local notation "rad" => Chess.Array.root R (T:=Tʳ) (tile F)

lemma geometric : (∏ i : (tiling he).Cell, rad (selector (black he) i))^2 = ‖R.Z‖ * Wilson.partition su n R.β := by
  let S := black he
  let f : Site n → ℝ := fun i => rad (selector S i)
  have hf : ∏ i, f i=rad true^S.card * rad false^(Sᶜ).card := by
    rw [← prod_mul_prod_compl S]
    congr 1
    · rw [← Finset.prod_const]; apply Finset.prod_congr rfl; intro i hi; unfold f; rw [show selector S i=true from decide_eq_true hi]
    rw [← Finset.prod_const]; apply Finset.prod_congr rfl; intro i hi; unfold f; rw [show selector S i=false from decide_eq_false (mem_compl.mp hi)]
  change (∏ i : Site n, f i)^2=_
  rw [hf,mul_pow,← pow_mul,← pow_mul,← half_colors he, double he, powering,powering, all_filled R he,blank R he,mul_comm]

include he in
lemma pressure (hk : 0 ≤ R.β) (hn : 4 ≤ n.val) :
    Wilson.partition su n R.β * volumeMass R ^ Fintype.card (Site n) ≤ R.Z.re := by
  let S := black he
  have hp : (∏ i:(Tʳ).Cell, rad (selector S i))^2=‖R.Z‖ * Wilson.partition su n R.β := geometric R he
  have hh : Fintype.card (Site n)=(Sᶜ).card*2:= by have hv:=double he; rw [half_colors he] at hv; exact hv.symm
  have hb := partition_pos (G:=su) (n:=n) R.β
  have hv := volumeMass_nonneg R
  have hc := tiles (selector S) (pattern R he) (show (Tʳ).kind=.link from rfl) hk hn
  rw [reading S R he (covers he)] at hc
  have hx := (pow_le_pow_left₀ (mul_nonneg hb.le (pow_nonneg hv _)) hc 2).trans_eq hp
  let C := (Tʳ).bandCut 0 timeAxis
  have hs : 2 ≤ C.half.val:=by have ht:= C.even; omega
  have hZ : 0 ≤ R.Z:= Regulator.Z_nonneg (C:=C) rfl hk hs
  have hZ' : ‖R.Z‖=R.Z.re:=(congr_arg (‖·‖) R.Z_real).trans ((Complex.norm_real _).trans (Real.norm_of_nonneg (Complex.le_def.mp hZ).1))
  rw [mul_pow,← pow_mul,← hh,hZ'] at hx
  apply le_of_mul_le_mul_left _ hb
  rw [mul_comm R.Z.re] at hx; rwa [sq,mul_assoc] at hx -- maybe hb relation etc

/-- No common mass/even number of flavor copies restriction. -/
theorem lower (hk : 0 ≤ R.β) (he' : Even n.val) (hn : 4 ≤ n.val) :
    (↑(Wilson.partition su n R.β * ∏ i, (4+R.m i)^(12*n.val^4)) : ℂ) ≤ R.Z := by
  have hl := pressure R (l:=⟨n.val/2, by omega⟩) (by obtain ⟨_,h⟩:=he'; change n.val = _ * (n.val / 2); omega) hk hn
  rw [R.Z_real]; rw [Complex.real_le_real]
  convert hl using 1; unfold volumeMass; rw [site_card, ← Finset.prod_pow]; congr 1; apply Finset.prod_congr rfl; intro i _; rw [pow_mul,add_comm (4:ℝ)]

/-- Strict normalization on any such trajectory regardless of nondegeneracy,
except the special zero-onsite-value case m_i = -4. -/
theorem nonzero (hk : 0 ≤ R.β) (he' : Even n.val) (hn : 4 ≤ n.val) (H : ∀ i, R.m i + 4 ≠ 0) : 0 < R.Z := by
  rw [R.Z_real]; rw [← Complex.ofReal_zero,Complex.real_lt_real]
  exact (mul_pos (partition_pos _) (pow_pos (volumeMass_positive R H) _)).trans_le
    (pressure R (l:=⟨n.val/2,by omega⟩) (by obtain ⟨_,h⟩:=he'; change n.val = _ * (n.val / 2); omega) hk hn)

end YM.Massive.Checker
#print axioms YM.Massive.Checker.lower
#print axioms YM.Massive.Checker.nonzero
