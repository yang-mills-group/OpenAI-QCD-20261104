import YM.Poised.Laminas
/-! # vector price statement, all columns.Mint -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k n:ℕ}{c l:Side}
namespace Stative
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
open PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource
variable {K: KernelChoices}
open Counting Counting.Click Display Costs Sieve Chute PhysicalNext.Repeat PhysicalNext.Repeat.Brim
lemma restored (u d Pk D':ℕ)(i:Rings d): ∃ C:ℝ,0 ≤ C ∧ ∀ {j k c l} (P:Flight j k)(h:l.val=c.val*P.L.val)(K:KernelChoices)(T:Tube su (Flight.visit P K h))(R:BudgetPoint)(F:Grid l→Lat.Fields l 6)(Z:Grid c → Lat.Fields c 6)(Y:Support c)(o :Site c)(H:TaperHol)(b:Cover)(x D t:ℝ)(A Q:Pol d), Q∈UV.cap d→A ∈ UV.cap d → Beacon.ActionTest H b (Chute.kite P h T F Y) Q → Beacon.ActionTest H b Z A → LocalOn Y Z→ ContDiffAt ℝ d (Z∘increment 1) 0 → ContDiffAt ℝ d (F∘ increment 1) 0 → o ∈Y → coverNumber (radiusB x) Y ≤ radiusB x → separation o (wrap c b) ≤ u→R.threshold ≤ 2 * fiery su x P.L → R.power=Pk → surface d ≤D' → d*d ≤ R.power →0<t → 0≤D → (∀ j:Λ d,∀ i:ℕ,i≤d →∀ α:Directions su c,R.dirBound o α→ ‖α‖ ≤ canopyW su P.L R.power x → ‖leftDerivs (framesF (purseX o D' t)∘ mantel j.val ∘ Z) (List.replicate i α) 1-leftDerivs (framesF (purseX o D' t)∘ Fountain.cherub T (flareV (proton P h)) (mantel j.val ∘ F)) (List.replicate i α) 1‖ ≤ D) → ‖fare i A R.threshold t - fare i Q R.threshold t‖ ≤ C*D:=by
    let p:=weight i.val; have hp:p≤d:=(Set.Finite.mem_toFinset (weightFinite d)).mp i.property; choose C hC H using fun J:Labels.Jet su=> verified u Pk p d D' J hp; obtain ⟨B,hB,G⟩:=shot (d:=d) C p hC; refine ⟨B,hB,?_⟩; intro j k c l P h K T R F Z Y o H0 b x D t A Q hQ hA ht ha hu hr hf hy hc he hR hk hβ hα hθ hD hv; let z:=R.threshold; rw [fare,fare, ← map_sub]; apply G _ D hD (Submodule.sub_mem _ (sizes_cap _ _ _ hA) (sizes_cap _ _ _ hQ)) _ i rfl; intro J; rw [map_sub,map_sub,smul_sub]; rw [← faithfulQ (t:=t) (q:=z) J H0 Z A ha p hp, ← faithfulQ (t:=t) (q:=z) J H0 _ Q ht p hp]; exact H J P h K T R F Z Y o H0 b x D t hu hr hf hy hc he hR hk hβ hα hθ hD hv
-- Project cost norm in Flame arbitrary rooted charge.No vector diminish off L. orientation through renewal.Wealth.
lemma chapter (d k D' n:ℕ)(v:Rings d) (hs:surface d≤D')(hd:d ≤ k)(hP:d*d ≤ n)(F:Basis (Fog d) ℂ (Label d)) : ∃ C:ℝ,0 ≤ C ∧ ∀ (H:TaperHol)(c:Side)(X:Grid c→Lat.Fields c 6) (b:Cover)(V:Support c)(R:BudgetPoint)(z:ℕ)(t x:ℝ), R.power=n → R.order=k→ Flame X R V (wrap c b) t D' z x → Fintype.card (ZBand d)<z →0<t → ∀ y:Pol d,y∈UV.cap d → Beacon.ActionTest H b X y → ‖fare v y R.threshold t‖ ≤ C*x:=by
    let p:= UV.weight v.val; have hp:p ≤ d:= (Set.Finite.mem_toFinset (weightFinite d)).mp v.property; choose C hC H using fun J:Labels.Jet su=> curvatureD d p J hp; let Y:=penny d; have hy:0 ≤ Y:=by unfold Y penny; positivity
    let W:=Λ d; let N:ℝ:= Fintype.card W; let A J:=N*C J*Y; have hA(J) :0 ≤ A J:= by unfold A N; positivity [hC J]
    obtain ⟨B,hB,h⟩:=shot (d:=d) A p hA; refine ⟨B,hB,fun H0 c X b V R z t x hX hV hx hz ht y hy' hY=>h _ x hx.sight.travels (sizes_cap _ _ _ hy') ?_ v rfl⟩; intro J; rw [← faithfulQ J H0 X y hY _ hp]; let Q:= R.threshold; let F:=purseX (wrap c b) D' t; have hν:0 ≤ x:= hx.sight.travels; have hZ :d≤ R.order:=hV.symm ▸ hd; let a:=(1:Grid c); have hh:Healthy Q V a:=Next.Foundations.one_healthy _ _ R.threshold_pos.le; have hp':ContDiffAt ℝ d (X∘increment 1) 0:= (hx.sight.use _ hh).of_le (Nat.cast_le.mpr hZ)
    have h1(i:W):‖rayE d p t H0 b (Q • J) (mantel i.val ∘ X)‖ ≤ C J*(Y*x):=by
       let Xq:=mantel i.val ∘X; let v:= stageZ (d:=d) H0 c b t; let L:=(v.restrictScalars ℝ).toContinuousLinearMap; have he:ContDiffAt ℝ d (Xq ∘increment 1) 0:=(mantel (A:=Faces (Site c)) i.val).contDiff.contDiffAt.comp _ hp'
       refine H J c Xq b H0 R t (Y*x) (mul_nonneg hy hν) (hX.symm ▸ hP) (L.contDiff.contDiffAt.comp _ he) ?_; intro k hk α hα; let s:=List.replicate k α; have hp:s.length≤d:= (List.length_replicate ..) ▸ hk
       have hg:=hx.issues i (Nat.lt_of_lt_of_le i.isLt hz) |>.2 a hh s (hp.trans hZ) (fun i hi=>(List.mem_replicate.mp hi).2.symm ▸ hα); rw [Push.Local.left_linear (framesF F) s he hp] at hg
       change ‖leftDerivs (L∘Xq) s 1‖ ≤ _; rw [Push.Local.left_linear L s he hp]; let p:=leftDerivs Xq s 1; refine (lots H0.T b t p ht.le hs).trans (mul_le_mul_of_nonneg_left ?_ hy); apply (march_view _ (wrap c b) (wrap c b) p D' t ht).trans; simpa only [separation_self,Nat.cast_zero,add_zero,one_pow,one_mul]
    rw [foundT (rayE _ _ _ _ _ _ _)]; apply (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=> C J*(Y*x)) (fun i _=>by rw [← glazeG X H0 _ hp i.val hp']; exact h1 i)).trans_eq ?_); rw [sum_const,card_univ,nsmul_eq_mul]; change N * (C J*(Y*x))= N*C J*Y*x; ring
-- Covector verifier.Expr. choose arbitrary use.Info.
end Stative
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Stative.chapter
#print axioms YM.Massive.Poised.Stative.restored
