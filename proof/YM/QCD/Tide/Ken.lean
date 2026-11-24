import YM.QCD.Tide.Patron
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f : Side}{F:ℕ}{β:ℝ} {R:Cells.Cut c} {K:KernelChoices}
open Flume YM.Next.Free Kites Acre Rails Rain Loom Fleet
variable {i j:ℕ} {Q: Patch} {V U:Pixel c F}
lemma journey (t:ℝ)(x:Stud c F): Tide.fresh (t • U) x=t • Tide.fresh U x:=by
     unfold Tide.fresh; rw [← integral_smul]; apply integral_congr_ae; apply ae_of_all; intro i; simp only [Pi.smul_apply]; rw [show Cove.light _ (t • U i)= (t:ℂ) • Cove.light _ (U i) from map_smul (Cove.light _) (t:ℂ) (U i),smul_mul_assoc,map_smul]; rfl
lemma staysS {X Y:Set (Site c)}(x:Stud c F)(h:Uses X x)(hp:X⊆Y):Uses Y x:=by
      refine ⟨fun U V hi=> h.1 U V (agrees_mono hi hp),fun U=>?_⟩; obtain ⟨v,hv⟩:=h.2 U; let q: RP.Deck X F→RP.Deck Y F:= fun i=> ((⟨i.1.1.val,hp i.1.1.property⟩,i.1.2),i.2); exact ⟨Grass.pass q v,hv.trans (AlgHom.congr_fun (Grass.pass_comp q (setDay Y)).symm v)⟩
lemma bandit (C:Lat.Cut c F)(h:C.t=0)(hp:0 ≤ C.β)(Y:Pixel c F)(hx:∀ U,Cove.light _ (Y U)=primalD c F C.β C.m U) (hh: 0 ≤ (Cvol Y).re): Healing Q (money Y):=by
     constructor; intro R hv he x hK hL hS; unfold money; rw [journey]; refine smul_nonneg (inv_nonneg.mpr hh) ?_; rw [← tallC x C h]; apply (crowned hv he hp x (staysS x hS (eaveH _ hv)) hK hL).trans_eq; unfold Tide.fresh; congr 1
     funext i; unfold measureK; rw [hx i]; unfold primalD; rw [show ∀ A: Grid c,bareD 0 A C.m = bareD C.t A C.m from fun A=>by rw [h]]; change _=ber _ (((bare C.β i:ℂ) • _)*_); -- edit
     rw [smul_mul_assoc,map_smul]; rfl
-- limit stability (all measurable)
lemma heats (X:ℕ→Pixel c F)(h: ∀ᶠ n in atTop,Continuous (X n) ∧ ∀ i,‖X n i‖ ≤ β)(hx:∀ i,Tendsto (fun n=> X n i) atTop (𝓝 (U i)))(hp:∀ᶠ n in atTop,Healing Q (X n)): Healing Q U:=by
    constructor; intro R hR hm x hx' hg hh; let Z:= tallH R x*x
    refine ge_of_tendsto (x:=atTop) (f:=fun n=>Tide.fresh (X n) Z) ?_ (hp.mono fun n hi=> hi.rails R hR hm x hx' hg hh)
    have hz: Stays Z:= (tallCost (R:=R) x hx').mult hx'
    obtain ⟨A,hA⟩:=hz.bounded; let p (X:Cove.EvenA c F)(Y:Fields c F):= ber _ (Cove.light _ X * Y); let f(Y:Pixel c F):= fun i=>p (Y i) (Z i); change Tendsto (fun n=>∫ i,f (X n) i ∂prior su c) _ (𝓝 (∫ i,f U i ∂_)); apply tendsto_integral_filter_of_dominated_convergence (fun _=> β*A) _ _ (integrable_const _) _ -- check
    · refine h.mono fun n q=>?_ ; exact (((stays ((Cove.lightC _).comp q.1)).mult hz).flows ((ber _).continuous_of_finiteDimensional)).mes.aestronglyMeasurable
    · refine h.mono fun n q=> ae_of_all _ fun i=>?_ ; change ‖ber _ (Cove.light _ (X n i)*Z i)‖ ≤ _; exact (Grass.price _).trans ((norm_mul_le ..).trans (mul_le_mul (q.2 i) (hA i) (norm_nonneg _) ((norm_nonneg _).trans (q.2 i))))
    refine ae_of_all _ fun i=>?_ ; exact ((ber _).continuous_of_finiteDimensional.continuousAt.tendsto.comp (((Cove.lightC _).continuousAt.tendsto.comp (hx i)).mul_const (Z i)))
end YM.QCD.Tide
