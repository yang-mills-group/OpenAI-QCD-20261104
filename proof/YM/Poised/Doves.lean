import YM.Poised.Furls
/-!
# Elevating and summing lens expenditures.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n m r:ℕ}{c l:Side}
namespace Pipes
open Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource
open Lining Lining.Ferry YM.Next.Free Pressure Garden QCD.Fork Leaf Tee Flume Kit Run Laurent Heir AnalyticBridge.SectorAffine.Offset Planned.AtomRegular Push.Uniform
local notation "F'"=> Lat.Fields c 6
local notation "F₁"=> Lat.Fields l 6
local notation "Y"=> Faces (Site c)
lemma registerL (w:ℝ)(hw:0<w)(i:Site c)(p:ℕ)(h:2≤p)(x:F'): plank i w x ≤ load (purseX i p w) x:=by
    rw [Stew.plank,pricesD _ hw.le,dry (purseX i p w) (purse_pos i p w hw)]; apply sum_le_sum; intro j _; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); unfold starch; have hu k:purseX i p w k=w*(1+(Stew.lens i k:ℝ))^p:=rfl; simp_rw [hu]; rw [prod_mul_distrib,prod_const]; have hx:(1+((j.sup (Stew.lens i):ℕ):ℝ))^2=(pieD (Stew.lens i) j:ℝ):=by unfold pieD; push_cast; rfl
    rw [←hx,mul_comm ((1+_)^2)]; apply mul_le_mul_of_nonneg_left _ (by positivity)
    by_cases he:j=∅; · simp [he]
    obtain ⟨u,hu,hh⟩:= j.exists_mem_eq_sup (Finset.nonempty_iff_ne_empty.mpr he) (Stew.lens i); have he(z:Y):1≤(1+ (Stew.lens i z:ℝ))^p:=one_le_pow₀ (by simp);
    rw [hh,← Finset.mul_prod_erase _ _ hu]; apply le_trans (pow_le_pow_right₀ (by simp) h); apply le_mul_of_one_le_right (zero_le_one.trans (he _)); exact Finset.one_le_prod fun i _=>he i
open MassiveQCD.Plate
variable (F:Grid c→ Lat.Fields c 6) {P:BudgetPoint}{V:Support c}{o:Site c}{x p y u:ℝ}
noncomputable abbrev capSpill (n:ℕ)(x:ℝ)(o:Site c) : F' →L[ℝ] F':= ((bias (Stew.lens (N:=6) o) x).restrictScalars ℝ).comp (spill n)
lemma achieve (n:ℕ)(b:ℕ→ℝ) (t p₀:ℝ)(hx:Sight V o 2 P x F p₀)(hp:0≤t)(hv:0<x)(hk:2≤ k) (ht:∀ i<n, P.supBounds o V (framesF (purseX o k x) ∘ (mantel i ∘ F)) (b i))(h:P.supBounds o V (capSpill n x o∘ F) t) (hu:t+ (∑ i∈range n,b i) ≤ u): Flame F P V o x k n u:=by
   have hg:0≤∑ i∈range n,b i:= Finset.sum_nonneg fun i hi=> (ht i (mem_range.mp hi)).1
   have hU:0≤u:= (add_nonneg hp hg).trans hu
   refine ⟨{hx with travels:=hU,pole:=?_},?_⟩
   · intro V hV L hL hA
     let A:= leftDerivs F L V; rw [viewSen _ _ _ hv.le]; change plank _ _ A ≤ _; rw [show A=spill n A+∑ i∈Finset.range n,panel i A from by rw [seldom,sub_add_cancel]]
     have hZ : plank o x (spill n A) ≤ t:=by
        change ‖capSpill n x o A‖≤ _; unfold A; rw [← Push.Local.left_linear _ _ (hx.use V hV) hL]; exact h.2 V hV L hL hA
     apply ((Brick.vested ..).trans (add_le_add hZ _)).trans hu; refine (vc_sum (Stew.lens o) ..).trans (sum_le_sum (fun i hi=>?_))
     apply (registerL x hv o k hk (panel i A)).trans; let Z:=(framesF (purseX o k x)).comp (mantel i); change ‖Z A‖ ≤_; unfold A; rw [← Push.Local.left_linear Z _ (hx.use V hV) hL]; exact (ht i (mem_range.mp hi)).2 V hV L hL hA
   intro i hi; have H:=ht i hi; refine ⟨hU,fun x hx j hj hV=>(H.2 x hx j hj hV).trans ?_⟩; apply le_trans _ hu; exact (Finset.single_le_sum (fun i hi=> (ht i (mem_range.mp hi)).1) (mem_range.mpr hi)).trans (le_add_of_nonneg_left hp)
end Pipes
end YM.Massive.Poised
