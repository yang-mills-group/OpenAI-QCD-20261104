import YM.Dart.Hill
import YM.Lust.Halo
/-!
  Coupon in box probes. Genuine average pair without requiring universal quadrature assumptions. Surjectivity can then pass through linear algebra on EXACT labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub Intag Intag.Vale
open Finset UV Poised Poised.Plans Poised.Plans.Stamp Poised.Stative
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C) {d:ℕ}
local notation "S"=> C.S
set_option quotPrecheck false
local notation "a" i:arg=> C.S.spacing (C.N i)
local notation "N" i:arg=> C.S.side (C.R i) (C.N i)
open CardsT
variable {P}
namespace GaugeP
variable {Z:Laurel d}{J:Landing P.sym Z}(K:GaugeP P Z J)
variable {β ν:ℝ}(hp:C.Path β ν)
-- incoming detector.
structure LensZ (P: Calibration C) (Z:Laurel d)(J:Landing P.sym Z)(u:Averaging) where
    g:ℕ→Stokes d→Label d
    h:ℕ→Stokes d→Label d
    T: ℝ
    pos :0 ≤ T
    tallest : ∀ᶠ i in atTop,∀ t:Stokes d, ‖g i t‖ ≤ T ∧ ‖h i t‖≤ T
    ℓ:ℕ
    x:Cover
    d0:ℝ
    he :0 < d0
    gap : d0 + 400*C.S.spacing ℓ ≤ ‖digit (C.S.spacing ℓ) x‖
    sees : ∀ᶠ i in atTop, nearG P.sym Z J.ε (fun t v:Stokes d=> let K:=ratioTo C.S (C.N i) ℓ; (C.A i).regulator.average (CardsT.checkedT u K (stemV P d i u (g i t)) 0 * CardsT.checkedT u K (stemV P d i u (h i v)) x))
namespace LensZ
variable {u:Averaging}(H:LensZ P Z J u)
include hp
local notation "ρ"=> C.S.spacing H.ℓ
local notation "γ" i:arg=> flex C.S H.ℓ (C.N i)
local notation "v" i:arg=> ratioTo C.S (C.N i) H.ℓ
noncomputable abbrev specR {C:Sequence} (i:ℕ)(X Y:stalk C i)(u vv:Cover):ℂ:=((C.A i).regulator).average (X u*Y vv)
noncomputable def checkP (i:ℕ)(X Y:stalk C i):ℂ := ((C.A i).regulator).average ((checkedT u (v i) X 0)*checkedT u (v i) Y H.x)
lemma fore :∃ e:ℝ,0 < e ∧∀ᶠ i in atTop,∀ t w:↥(box (flex C.S H.ℓ (C.N i))), localSep C i (![t.val,ratioTo C.S (C.N i) H.ℓ • H.x+w.val]:Fin 2→ Cover) e:=by
    let U:= C.S.spacing H.ℓ; let k:=digit U H.x; let V:= 400 * U + ‖k‖
    refine ⟨H.d0/2,half_pos H.he,?_⟩; filter_upwards [hp.uv.tendsto_atTop.eventually_ge_atTop H.ℓ, fullPrice hp H.d0 V] with i hi hh t w
    let f:=digit (a i); let b:= v i • H.x+w.val; have h : f b = k+f w.val:= by unfold f b; rw[digit_plus,← GaugeP.gears hi]
    have hw: ‖f t.val‖≤ 200*U:= port i H.ℓ hi _ t.property; have hhW: ‖f w.val‖ ≤ 200*U := port i H.ℓ hi _ w.property
    have hz: f t.val - f b = (f t.val-f w.val)-k:=by rw[h]; abel
    have he : H.d0 ≤ dist (f t.val) (f b)∧ dist (f t.val) (f b) ≤ V:=by
         rw [dist_eq_norm,hz]; have hx:= norm_sub_le (f t.val-f w.val) k; have ht:= norm_sub_le (f t.val) (f w.val); have hf:= norm_sub_le (f t.val-f w.val) (f t.val-f w.val-k); rw[sub_sub_self] at hf; have hy: H.d0+400*U ≤‖k‖:=H.gap; unfold V
         constructor<;> linarith only [hw,hhW,hf,hx,ht,hy]
    have hh:= hh t.val b he.1 he.2; intro t k ht; fin_cases t <;> fin_cases k <;> first| contradiction|exact hh| rwa [separation_comm] at hh
omit hp
-- ℝ convex budgets for DISTINCT pair readers even if weights vary.
lemma bill {i:ℕ}(he:H.ℓ ≤ C.N i)(X Y:stalk C i)(V:ℝ)(hX:∀ t w:↥(box (flex C.S H.ℓ (C.N i))), ‖specR (C:=C) i X Y t.val ((v i) • H.x+w.val)‖≤V): ‖checkP H i X Y‖ ≤ V:=by
    obtain ⟨F,hf,h,hF⟩:= strummed C.S 0 u X he; obtain ⟨G,hg,hw,hG⟩:= strummed C.S H.x u Y he; unfold checkP checkedT; rw[hF,hG]; let I:= ↥(Lattice.box (flex C.S H.ℓ (C.N i))); change ‖((C.A i).regulator).average ((∑ j:I,(↑(F j):ℂ) • X _)*(∑ j:I,(↑(G j):ℂ) • Y _))‖≤_
    rw [Finset.sum_mul,map_sum]; apply (norm_sum_le ..).trans; apply le_trans (b:=∑ i:I,F i*V); swap; · rw [← Finset.sum_mul,h, one_mul]
    apply Finset.sum_le_sum; intro j _; rw [← show X _=X _ from (show X j.val=X ((v i) • (0:Cover)+j.val) from (by simp)),smul_mul_assoc,map_smul,norm_smul, Complex.norm_real, Real.norm_of_nonneg (hf j)]; apply mul_le_mul_of_nonneg_left _ (hf _); rw [Finset.mul_sum,map_sum]; apply (norm_sum_le ..).trans; apply le_trans (b:=∑ i:I,G i*V); swap; · rw[← Finset.sum_mul,hw,one_mul]
    apply Finset.sum_le_sum; intro t _; rw [mul_smul_comm,map_smul,norm_smul, Complex.norm_real, Real.norm_of_nonneg (hg t)]; exact mul_le_mul_of_nonneg_left (hX _ _) (hg t)
-- heightH linear in second slot. Convenient for rank.
variable (i:ℕ)(X:stalk C i)
open Rolls
noncomputable def checkLinear (he:H.ℓ ≤ C.N i): stalk C i→ₗ[ℂ]ℂ where
    toFun:=fun y=> checkP H i X y
    map_add' y z:=by
         obtain ⟨I,hI,hN,p,t,hp,hw,h1,h⟩:= constitution (X:=Insertion (N i) 6) u (viewW C.S (C.R i) he)
         rw [show (viewW C.S (C.R i) he).count.val=v i from rfl] at h
         unfold checkP checkedT; rw [show Averaging.filter u (v i) (y+z) ((v i) • H.x) = Averaging.filter u (v i) y ((v i) • H.x)+Averaging.filter u (v i) z ((v i) • H.x) from (?_),mul_add,map_add]
         rw [h (y+z) ((v i) • H.x),h y ((v i) • H.x),h z ((v i) • H.x)]; simp only [Pi.add_apply,smul_add,Finset.sum_add_distrib]
    map_smul' z y:=by
         obtain ⟨I,hI,hN,p,t,hp,hw,h1,h⟩:= constitution (X:=Insertion (N i) 6) u (viewW C.S (C.R i) he)
         rw [show (viewW C.S (C.R i) he).count.val=v i from rfl] at h
         unfold checkP checkedT; rw [show Averaging.filter u (v i) (z • y) ((v i) • H.x) = z • Averaging.filter u (v i) y ((v i) • H.x) from (?_),mul_smul_comm,map_smul]; rfl
         rw [h (z • y) ((v i) • H.x),h y ((v i) • H.x),Finset.smul_sum]; exact sum_congr rfl fun i _=> (smul_comm (↑(p i):ℂ) z _)
end LensZ
end GaugeP
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GaugeP.LensZ.checkLinear
#print axioms YM.Massive.Needle.GaugeP.LensZ.fore
#print axioms YM.Massive.Needle.GaugeP.LensZ.bill
