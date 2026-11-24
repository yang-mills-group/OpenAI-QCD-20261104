import YM.Massive.Finite.Squares
import YM.QCD.Plum.Rind

/-!
# Adapted-seam link Reflection for all Borel Grassmann tests on the unequal mass regulator

Upgrades `raw_reflection` to gauge-invariant bounded Borel pencils. Explicit `Uses`
a la `Tide`. Real bare masses arbitrary across flavors. Grassmann numerator
in the order theta x · x; prior Haar; do not require probability positivity of
gauge marginal to prove. This will be used in multi-step blocking.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive
open QCD QCD.Lat QCD.Grass Lattice Wilson MeasureTheory Function QCD.Tide QCD.Acre.Rails
open QCD.RP
open scoped BigOperators Topology Matrix.Norms.Frobenius ComplexOrder
variable {n : Side} {F : ℕ} {R : Regulator n F} {C : Cells.Cut n}
namespace Regulator
lemma crown_mult (K:Lat.Cut n F)(x y:Stud n F): crown C K (x*y)=crown C K y*crown C K x:=by
    funext i
    let px:Insertion n F:= ContinuousMap.const _ (x (C.pullC su i)); let py:Insertion n F:= ContinuousMap.const _ (y (C.pullC su i))
    exact DFunLike.congr_fun (pic_mul (R:=C) (C:=K) px py) i

lemma floors_uses (x:Insertion n F)(S:Set (Site n))(h:Floors S x): Uses S (⇑x):=by
    obtain ⟨f,hF,h,H⟩:=h
    refine ⟨fun U V he=> (H U).trans ?_, fun U=>⟨f U,H U⟩⟩; rw [h U V he]; exact (H V).symm
local notation "Ω"=> prior su n
lemma signed (h:C.kind=.link)(hb:0≤R.β)(hl:2 ≤ C.half.val)(x : Stud n F)(hS:Plum.Fence C.sector x):
    0 ≤ joint ((⇑R.density) * (crown C R.zeroCut x*x)):=by
  classical
  let S:= Finset.univ.filter fun i:Site n=> i∈C.sector
  have hT : (S:Set _)=C.sector:=by ext; simp [S]
  let p:Insertion n F:= Onsite.patch R.m S
  let q:Insertion n F:= picture C R.zeroCut p
  let f:= x*⇑p; let g:= crown C R.zeroCut x
  have hu : Plum.Fence C.sector ⇑p:=⟨stays p.continuous, floors_uses p C.sector (Onsite.floors R.m hT.le),fun k U=>DFunLike.congr_fun (Onsite.patch_invariant R.m S k) U⟩ -- note invariant k arg
  have he: Plum.Fence C.sector f:= hS.mult hu
  refine (crowned (C:=R.zeroCut) h hl (show 0≤ R.zeroCut.β from hb) f he.he he.hp he.hz).trans_eq ?_
  unfold joint; apply integral_congr_ae; apply ae_of_all; intro i
  have hf: crown C R.zeroCut f = ⇑q*g:= crown_mult ..
  unfold measureK; rw [hf, R.compareDensity, squares h R hT];
  have hx: q i* g i*(x i*p i)= q i*p i*(g i*x i):= by
      rw [mul_assoc,mul_assoc, ← mul_assoc (g i) (x i) (p i), (show g i*x i*p i=p i*(g i*x i) from (Onsite.plus R.m S i).central _)]
  change (bare R.β i:ℂ)*ber _ (R.zeroCut.insertD i *(q i*g i * (x i*p i)))= ber _ (((common R.zeroCut).density i*(q i*p i))*(g i*x i))
  rw [hx,mul_assoc ((common ..).density i), density_apply, smul_mul_assoc,map_smul]; rfl

-- `tallH` works when the run's bare seams are all based at 0.
lemma base_health (P:Acre.Rails.Pixel n F)(J:RG.Patch)(hp:0 < Rain.Cvol P)
    (hZ:Cove.light _ ∘ P= ⇑R.density)(ht:R.t=0)(hb:0≤R.β): Healing J (money P):=by
    constructor; intro R' hv he x hx hz hU; unfold money; rw [journey];
    refine smul_nonneg (inv_nonneg.mpr ((Complex.lt_def.mp hp).1.le)) ?_
    rw [← tallC x R.zeroCut (show R.zeroCut.t= 0 from ht)]
    change 0 ≤ joint ((Cove.light _ ∘ P) * (crown _ _ x*x)); rw [hZ]; exact signed hv hb he _ ⟨hx, staysS x hU (eaveH _ hv),hz⟩
end Regulator
end YM.Massive
#print axioms YM.Massive.Regulator.base_health
