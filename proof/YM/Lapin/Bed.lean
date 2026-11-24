import YM.Lapin.Zass
/-!
  billing honest even accompaniment.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MassiveQCD.Sample.Basal
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC Massive.PCAC.Oren
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k:ℕ}{I D:Type}[Fintype I]{a t b w x v θ m:ℝ}
variable (o u: Site c) {U:BudgetPoint}(a:Flavor 6)(i:Axis)
open Entr Entr.Meridian
namespace WindowU
noncomputable def cashZ (v w:ℝ):= 4*(v^2*veinFare 1)* Real.exp (w*81)
local notation "Q"=> mote a u
local notation "V"=> halo 1 ({o} : Support c)
lemma pinnedZ (hus:u∈V) (hv:0<v)(hw:0≤w) : Given o U v w (cashZ v w) (cashZ v w) (mote a u):=by
        let P:ℝ:= 4*(v^2 * veinFare 1); let Q':=mote a u; let ν:=Q' 1; let f:Unit→ℝ:= fun _=>P
        have he(j:Site c)(hj:j∈V):separation j o ≤ 1:=by rw [separation_comm]; simpa [halo_spec] using hj
        have hδ(U): Creek.load (fun _=>v) ((Q' U).val)≤ v^2*veinFare 1:= by
             rw [show (Q' U).val= - form _ from rfl,load_neg]; refine (Port.fauna (localF u 1 a a) hv).trans_eq ?_; unfold Port.jacket; rw [veinSum]
        have hc: (coverNumber U.B V:ℝ) ≤ 81:=by
             have hp:coverNumber U.B V ≤ 81:=le_trans (Lattice.Corona.cover_mono (Lattice.Corona.halo_mono (show 1 ≤ 1*U.B from by rw [one_mul]; exact U.B_pos) subset_rfl) U.B) (Lattice.Corona.tile _ 1 _ U.B_pos); exact_mod_cast hp
        have hP:0≤P:=by unfold P veinFare; positivity
        have hs: Ac.Hit (fun _:Unit=> V) U.B f w (cashZ v w):=by
             intro i; refine budget_finite (fun x=> ?_) ?_; · split; exact mul_nonneg hP (Real.exp_pos _).le; exact le_rfl
             rw [Fintype.sum_unique]; split; next h=> unfold cashZ; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hc hw)) hP
             next h=> change 0≤ P*_; exact mul_nonneg hP (Real.exp_pos _).le
        have hz:Gated V ν:=by
             change -(form _ )∈_; apply Subalgebra.neg_mem; unfold form; apply Subalgebra.sum_mem; intro i _; apply Subalgebra.sum_mem; intro j _; by_cases h:i.1.1=u∧ j.1.1=u
             · apply Subalgebra.smul_mem; apply Subalgebra.mul_mem; exact Creek.marked _ _ (mem_filter.mpr ⟨mem_univ _,show j.1.1∈V from h.2.symm ▸ hus⟩); exact Creek.marked _ _ (mem_filter.mpr ⟨mem_univ _,show i.1.1∈V from h.1.symm ▸ hus⟩) -- arguments
             rw [show localF u _ _ _ i j=0 from ?_,zero_smul]; exact Subalgebra.zero_mem _; push_neg at h; by_cases hp:i.1.1=u; exact focusR _ _ _ _ _ _ (h hp); exact focusL _ _ _ _ _ _ hp
        have ht:Woven o V U v Q' P:=by
             change Woven o V U v (fun _=>ν) P; refine ⟨fun i j h=>rfl,fun i=>hz,fun _ _=>contDiffAt_const, ?_,measurable_const,hP⟩; intro X_ hw l hl h'; rw [Work.G07.left_const]; split
             next _=> apply (senCamp V he ν hv hz).trans; rw [Loom.pulse]; apply (mul_le_mul_of_nonneg_left (hδ 1) (by positivity : 0≤ (1+(1:ℕ):ℝ)^2)).trans; norm_num [P]
             next _=> rw [← measures,map_zero,norm_zero]; exact hP -- edit
        refine ⟨Unit,inferInstance,fun _=>V,fun _=>Q',f,f, by rw [Fintype.sum_unique],fun i U g=>κmolt a u U g,fun i=>halo_subset _ _ (mem_singleton_self _),fun _=>ht,hs,hs,fun i U=>?_⟩ -- arguments order
        apply (hδ U).trans; change _ ≤ P; unfold P; apply le_mul_of_one_le_left; unfold veinFare; positivity; norm_num
lemma Zgiving (hv:0<v)(hw:0 ≤ w) : Given o U v w (cashZ v w) (cashZ v w) (sprig a i o):=by
        have hh(p:Site c)(h:separation o p ≤1): p∈ V:=by simpa [halo_spec] using h
        let C:= cashZ v w; let p:=o+step i; let q:=o-step i; let x:= mote a p; let y:= mote a q
        have hm : sprig a i o= (2:ℂ)⁻¹ • (x+ (-1:ℂ) • y):=by rw [neg_one_smul,←sub_eq_add_neg]; rfl
        have hv1: q∈ V:=hh q (show separation o q≤1 from by unfold separation q; rw[sub_sub_cancel]; exact pdist_step _)
        have hz:= Given.units _ _ (Given.plies _ _ (pinnedZ o (o+step i) a (U:=U) (hh p (Work.E01.sep_step_le o i)) hv hw) _ (Given.units _ _ (pinnedZ o q a hv1 hv hw) (-1))) ((2:ℂ)⁻¹)
        rw [hm]; norm_num at hz ⊢; unfold x p y; convert hz using 1 <;> ring
end WindowU
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.WindowU.Zgiving
