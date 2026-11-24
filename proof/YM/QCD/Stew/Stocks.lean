import YM.QCD.Stew.Cipher
/-! # the actual supports in momentum extraction. Anchored real Lie jet norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ} {w r a u:ℝ}{p:BudgetPoint}{o:Site c}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset
variable {ι β:Type}{E:Gem c N ι}{b:Flavor N}
-- chart stock definition vector. bounds mix CL maps.
variable {B: Support c}{f₀ g' : Grid c→EvenA c N}
structure Woven (o:Site c)(X : Support c)(b:BudgetPoint)(v:ℝ)(f:Grid c →EvenA c N)(u:ℝ): Prop where
 room : LocalOn X f
 gated : ∀ i,Gated X (f i)
 use (V):Healthy b.threshold X V → Push.Local.Chart b.order f V
 pole :∀ V, Healthy b.threshold X V → ∀ l, List.length l ≤b.order → (∀ i∈l,b.dirBound o i) → Sen o v (RG.leftDerivs f l V)≤u
 Borel : Measurable f
 travel : 0≤u
variable (h : Woven o B p a f₀ u) -- replace v'
namespace Woven
include h
lemma stretches {A: Support c}(hx:B⊆A)(hp:u ≤ r): Woven o A p a f₀ r:=⟨fun _ _ hv=> h.room _ _ (agrees_mono hv hx),fun i=> gateMon _ _ hx _ (h.gated _),fun i hi=> h.use _ (hi.mono_left hx),fun i hi x hz hv=>(h.pole _ (hi.mono_left hx) x hz hv).trans hp,h.Borel,h.travel.trans hp⟩
lemma sizeU (V:Grid c)(hp : Healthy p.threshold B V):Sen o a (f₀ V) ≤ u:=h.pole _ hp [] (by simp) (by simp)
lemma addition (hh: Woven o B p a g' r):Woven o B p a (f₀+g') (u+r):=by
    refine ⟨fun V U hv=>congr_arg₂ (·+·) (h.room _ _ hv) (hh.room _ _ hv),fun i=>?_, fun i hi => (h.use i hi).add (hh.use i hi),?_, h.Borel.add hh.Borel,add_nonneg h.travel hh.travel⟩
    · unfold Gated; rw [Pi.add_apply,map_add]; exact Subalgebra.add_mem _ (h.gated _) (hh.gated _)
    intro i hi x hx he; rw [Push.Local.left_add x (h.use i hi) (hh.use i hi) hx, ← measures, map_add]; exact (norm_add_le ..).trans (add_le_add (h.pole i hi x hx he) (hh.pole i hi x hx he))
set_option maxHeartbeats 600000 in
lemma byScalar (k:ℝ) : Woven o B p a (k • f₀) (‖k‖*u):=by
    let M:EvenA c N→L[ℝ]EvenA c N:= LinearMap.toContinuousLinearMap { toFun:=fun i=> k • i,map_add':=fun i j=>smul_add .., map_smul':=fun j i=>smul_comm k j i }
    refine ⟨fun i j hi=> congr_arg (k • ·) (h.room i j hi), fun i=> Territory.club _ _ _ (h.gated i),fun i hi => M.contDiff.contDiffAt.comp 0 (h.use i hi),?_, measurable_const.smul h.Borel,mul_nonneg (norm_nonneg _) h.travel⟩
    intro i hi z hz hc; rw [show k • f₀=M ∘ f₀ from rfl, Push.Local.left_linear M z (h.use i hi) hz, ← measures]; let w:=leftDerivs f₀ z i
    let N':=needle o N a
    rw [show needle _ _ _ (M w)=k • N' w from map_smul (N'.restrictScalars ℝ) ..,norm_smul]; exact mul_le_mul_of_nonneg_left (h.pole _ hi z hz hc) (norm_nonneg _)
omit h
lemma sumX (v: ι →Grid c→EvenA c N)(s: Finset ι)(Q:ι→ℝ)(hp:∀ i∈s,Woven o B p a (v i) (Q i)): Woven o B p a (∑ i∈s,v i) (∑ i∈s,Q i):=by
    induction s using Finset.induction_on with
    | empty=> rw [sum_empty,sum_empty]; refine ⟨fun i j hi=>rfl,fun i=>Fleet.spruce B, fun i hi=>contDiffAt_const,?_,measurable_const,le_rfl⟩; intro V hp l hl hx; induction l generalizing V with
       | nil=> change Sen o a (0:EvenA c N)≤ _; rw [← measures,map_zero,norm_zero]
       | cons i l ih=> rw [show leftDerivs (0:Grid c→EvenA c N) (i::l) V= (0:EvenA c N) from (Work.G07.left_const (0:EvenA c N) (i::l) V), ← measures,map_zero,norm_zero]
    | insert i s hi ih=>rw [sum_insert hi,sum_insert hi]; exact (hp i (mem_insert_self ..)).addition (ih fun j hj=>hp _ (mem_insert_of_mem hj))
end Woven
-- star-width. universal ONE size-neighborhood in supports.
def stand (o:Site c):= halo 2 {o}
lemma stem (o:Site c)(i j:Site c)(p:Step)(hi:i=o)(hj:j=i+p.vec):i∈stand o∧ j∈stand o:=by
   subst o j
   have hp :separation (i+p.vec) i ≤ 1 :=by unfold separation; rw [add_comm i,add_sub_cancel_right]; rcases p with ⟨p,_|_⟩; exact Lattice.pdist_step _; change pdist (-step p:Site c) ≤ _; rw [pdist_neg]; exact pdist_step _
   exact ⟨halo_subset 2 _ (Finset.mem_singleton_self i), halo_spec.mpr ⟨i, Finset.mem_singleton_self i, by rw [separation_comm];omega⟩⟩ -- edit
lemma stackP (M:Sheet c)(h:∀ i j,i∉B ∨ j∉B → cell M i j=0)(N:ℕ): Gated B (Port.paleF N M):=by
    unfold Gated; rw [Port.serviceP]; unfold form; apply Subalgebra.sum_mem; intro i _; apply Subalgebra.sum_mem; intro j _; by_cases hp:i.1.1∈B ∧ j.1.1∈B
    · apply Subalgebra.smul_mem; apply Subalgebra.mul_mem <;> apply Creek.marked
      exacts [mem_filter.mpr ⟨mem_univ _,hp.2⟩,mem_filter.mpr ⟨mem_univ _,hp.1⟩]
    rw [show Lat.copies N M i j=0 from ?_, zero_smul]; exact Subalgebra.zero_mem _
    unfold copies; rw [Matrix.blockDiagonal_apply]; split; next he=> exact Matrix.ext_iff.mpr (h _ _ (by tauto)) i.1.2 j.1.2
    rfl
end YM.QCD.Stew
