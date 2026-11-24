import YM.Poised.Tariffs
import YM.Poised.Counting
/-! # finite orientation coordinate evaluations.Rotor all ports by same Gate -/
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
-- coefficient membership cost.E.Foundation.Weight lower uniform Norm.
def coord (i:PowerPair d):Pol d →ₗ[ℂ]ℂ:=(zBasis d).coord i
lemma menu (x:Pol d)(h:x∈UV.cap d)(k:PowerPair d)(he:coord k x≠0) : k∈chair d:=by
   by_contra ht; apply he; apply Submodule.span_induction (p:=fun i _=>coord k i=0) ?_ ?_ ?_ ?_ h
   · rintro _ ⟨p,hp,rfl⟩; rw [coord, ← minted]; have hx:k ≠ p:=fun hh=>ht (hh.symm ▸ (Set.Finite.mem_toFinset _).mpr hp); simp [hx,hx.symm]
   · rw [map_zero]
   · intro i j _ _ ha hb; rw [map_add,ha,hb,add_zero]
   intro a i _ h; rw [map_smul,h,smul_zero]
lemma reruns (x:Pol d)(h:x∈UV.cap d): x=∑ i∈chair d,coord i x • gen i:=by
   let p:=(zBasis d).repr x; have he:x= ∑ i∈p.support,p i • gen i:=by simp_rw [← minted]; exact ((zBasis d).linearCombination_repr x).symm
   apply Eq.trans he; exact sum_subset (show p.support⊆chair d from fun i hi=>menu x h i (Finsupp.mem_support_iff.mp hi)) (fun i _ hi=>by rw [show p i=0 from Finsupp.notMem_support_iff.mp hi,zero_smul]) -- coord
lemma rank_fee (p:PowerPair d)(x:Pol d)(a t:ℝ): coord p (Sieve.widths a t x)=(a:ℂ)^life p.1*(t:ℂ)^p.2.card* coord p x:=by
    suffices h : (coord p).comp (Sieve.widths a t)=((a:ℂ)^life p.1*(t:ℂ)^p.2.card) • coord p from DFunLike.congr_fun h x
    apply (zBasis d).ext; intro i; rw [LinearMap.comp_apply,minted,widths_m,map_smul, ← minted]; by_cases he:p=i <;> simp [coord,he,Ne.symm]
lemma geo_basis (p:PowerPair d)(x:Pol d)(k:ℕ): coord p (geometry k x)= if weight p=k then coord p x else 0:=by
   split; next h=>
      suffices he:(coord p).comp (geometry k)=coord p from DFunLike.congr_fun he x; apply (zBasis d).ext; intro i; rw [LinearMap.comp_apply,minted,geometry_basis]; split; rfl
      next hp=> rw [map_zero,← minted]; have h:p≠i :=fun ht=> hp (ht ▸ h); simp [coord,h,h.symm]
   next h=>
      suffices he:(coord p).comp (geometry k)=0 from DFunLike.congr_fun he x; apply (zBasis d).ext; intro i; rw [LinearMap.comp_apply,minted,geometry_basis]; split; next hp=> have h:p≠i:=fun ht=> h (ht.symm ▸ hp); rw [←minted]; simp [coord,h,Ne.symm]
      next _=> rw [map_zero,LinearMap.zero_apply]
abbrev fare (p:PowerPair d)(x:Pol d)(θ t:ℝ):= coord p (Sieve.widths θ t x)
lemma geom_cap {p:Pol d}(hp:p∈UV.cap d)(k:ℕ): geometry k p∈UV.cap d:=by
    apply Submodule.span_induction (p:=fun x _=> geometry k x∈UV.cap d) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨i,hi,rfl⟩; rw [geometry_basis]; split; next h=>exact Submodule.subset_span ⟨_,hi,rfl⟩
      next=> exact Submodule.zero_mem _
    · simp
    · intro x y _ _ h₁ h₂; rw [map_add]; exact Submodule.add_mem _ h₁ h₂
    intro a x _ h; rw [map_smul]; exact Submodule.smul_mem _ _ h
abbrev Rings (d:ℕ):= {p : PowerPair d // p∈chair d}
def line (d:ℕ): (Rings d→ℂ) →ₗ[ℂ] Pol d:= {toFun:=fun x=>∑ i:Rings d,x i • gen i.val,map_add':=fun x y=>by simp [add_smul, sum_add_distrib],map_smul':=fun a x=>by rw [smul_sum]; refine sum_congr rfl fun i _=>?_ ; simp [smul_smul]}
def guide (p:Pol d): Rings d→ℂ:=fun i=>coord i.val p
lemma quiet (p:Pol d)(hp:p∈UV.cap d) : line d (guide p)=p:=by
    change (∑ i:Rings d,_)=_; simp_rw [guide]; exact (Finset.sum_coe_sort (s:=chair d) (f:=fun x=>coord x p • gen x)).trans (reruns p hp).symm
lemma piecesL (q:Rings d)(u:Rings d): coord q.val (gen u.val)= if q=u then 1 else 0:=by rw [coord, ← minted]; by_cases he:q=u <;> simp [he]
lemma glory (x:Rings d→ℂ)(i:Rings d): coord i.val (line d x)=x i:=by
    change coord _ (∑ k:Rings d,_)=_; rw [map_sum]; simp_rw [map_smul,piecesL]; simp
lemma shot (b:Labels.Jet su→ℝ)(n:ℕ)(h:∀ i,0 ≤ b i): ∃ C:ℝ,0≤ C ∧ ∀ (p: Pol d)(M:ℝ),0≤M→ p∈UV.cap d → (∀ J:Labels.Jet su, ‖(n.factorial:ℂ) • ready d J (geometry n p)‖ ≤ b J*M) →∀ i:Rings d, weight i.val=n→ ‖coord i.val p‖ ≤ C*M:=by
    let f i:= (((n.factorial:ℂ) • ((ready d i).comp (line d))).restrictScalars ℝ).toContinuousLinearMap
    have he(x: Rings d → ℂ)(hp:∀ i,f i x=0): x=0:=by
        have hh:line d x=0:=distinct _ _ fun i=> smul_right_injective _ (show (n.factorial:ℂ) ≠ 0 by exact_mod_cast n.factorial_ne_zero) ((hp i).trans (by dsimp only; rw [map_zero, smul_zero]))
        funext i; exact (glory x i).symm.trans (hh ▸ map_zero _)
    obtain ⟨C,hC,H⟩:= budget_probes f he b h; refine ⟨C,hC.le,?_⟩; intro p M hM hp hv i hi
    let P:=geometry n p; have hP:P∈UV.cap d:=geom_cap hp n; have hx:∀ J,f J (guide P)=(n.factorial:ℂ) • ready d J P:=fun J=> by change (n.factorial:ℂ) • ready d J (line d (guide _))=_; rw [quiet P hP]
    apply (le_trans _ (H _ hM (guide P) fun j=>by rw [hx]; exact hv j)); have hi:guide P i=coord i.val p:= (geo_basis i.val p n).trans (if_pos hi); rw [← hi]; exact norm_le_pi_norm ..
-- comparison.Aplic.Trim ։
lemma pastL (p: Rings d)(H:TaperHol)(j k D' :ℕ)(V:Hera.Rights su n) (σ τ A:ℝ)(ha:0≤A)(hσ:0<σ)(hτ:0≤τ)(hV:d<n) : ∃ C:ℝ,0≤C ∧ ∀ (P:Flight j k)(K:KernelChoices)(c l:Side)(h:l.val=c.val*P.L.val)(T: Tube su (Flight.visit P K h))(R:BudgetPoint)(v u:ℕ)(X:Support l)(Y:Support c)(b b':Cover)(vi vo t M:ℝ)(z:ℕ), n ≤ R.order → Fintype.card (ZBand d) < z → Harbor X Y b b' T R σ τ A vi vo t u v →∀ (F:Grid l→ Lat.Fields l 6) (y:Pol d), Flame F R X (wrap l b) vi D' z M → y∈UV.cap d→Beacon.ActionTest H b' (kite P h T F Y) y →
    let m:=weight p.val; ‖fare p.val y t vo‖ ≤ C*ratioP d (n+1) v*M ∧ (∀ a:ℝ,0<a→T.R.A0=linesOf P a→ d/2≤j→(∀ k U,slots 6 k (F (Lattice.gauge k U))=F U)→ (∀ (J:Labels.Jet su)(k:ℕ), k < m → WardBin.leading k (Beacon.moment (d:=d) H b J F)=0)→∀ x:Pol d,x∈ UV.cap d → Beacon.ActionTest H b F x→ ‖fare p.val y t vo - (Kit.slope P.L:ℂ)^m * fare p.val x t vo‖ ≤ C*tar σ u * ratioP d (n+1) v*M):=by
    let f:=weight p.val; have ht:f ≤ d:= (Set.Finite.mem_toFinset (weightFinite d)).mp p.property; choose C hC H0 using fun J:Labels.Jet su=> sealR (j:=j) (k:=k) H J ha hσ hτ d D' V f ht hV
    obtain ⟨B,hB,hC0⟩:=shot (d:=d) C f (fun i=>zero_le_one.trans (hC i)); refine ⟨B,hB,?_⟩; intro P K c l h T R v u X Y b b' vi vo t M z hk hZ hq F y hM hp h' k0; have hw J:=H0 J P K c l h T R v u X Y b b' vi vo t M z hk hZ hq F hM; have he:0 ≤ratioP d (n+1) v:=by unfold ratioP pups; positivity
    have hMM:=hM.sight.travels; let fY:=Sieve.widths t vo y
    constructor
    · rw [mul_assoc]; exact hC0 fY (ratioP d _ _*M) (mul_nonneg he hMM) (sizes_cap t vo y hp) (fun J=>by rw [← faithfulQ J H _ _ h' _ ht]; exact (hw J).1.trans_eq (mul_assoc ..)) _ rfl
    intro a hA hK hX hg hF x hX' hx; let s:ℂ:= (Kit.slope P.L:ℂ)^f; let fx:=Sieve.widths t vo x; let C':= ratioP d (n+1) v * M
    have hf': fY-s • fx∈UV.cap d:= Submodule.sub_mem _ (sizes_cap t vo y hp) (Submodule.smul_mem _ _ (sizes_cap t vo _ hX'))
    have he': 0≤tar σ u:=by unfold tar; positivity
    have hu := hC0 _ (tar σ u*C') (by unfold C'; positivity) hf' (fun J=>?_ ) p rfl; swap
    · simp only [map_sub,map_smul,smul_sub]; rw [smul_comm (↑(f.factorial):ℂ) s]; rw [← faithfulQ (q:=t) (t:=vo) J H _ y h' f ht,← faithfulQ (q:=t) (t:=vo) J H _ x hx f ht]; rw [show s=(((Kit.slope P.L:ℝ)^f:ℝ):ℂ) from (Complex.ofReal_pow ..).symm]; exact ((hw J).2 a hA hK hX hg hF).trans_eq (by unfold C'; ring) -- second sealR doesn't take x
    rw [map_sub,map_smul] at hu; exact hu.trans_eq (by unfold C'; ring)
end Stative
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Stative.pastL
