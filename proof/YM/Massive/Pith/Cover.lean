import YM.Massive.Pith.Pensions
import YM.QCD.Finch.Dad
import YM.Massive.Commerce.Issue
/-! # Remnant. No site change; through-3 improvement for iterative bank. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false -- parallel unfold cases
noncomputable section
namespace YM.QCD.Pith
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Revolve Stew Reggae Brick Port Entr
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
variable (b:Flavor N)
local notation "J"=> Modes c N
variable {t r q:ℝ}{p:BudgetPoint}{ι α β:Type}
variable (o:Site c) (M:Spike)

variable (E:Gem c N ι)
variable (i:ι)(U:Grid c)
/-! # Correcting the old support shelves on flag mask
Carry constant subtraction to the unmasked global scalar, and the local phaseShelf to just its *root-good* mask. `branches` is the correction that must still be appended to preserve equality. This correction is Tall. No K gas is wasted here, the wallet absorbs it into the matcher again later. -/
namespace Tall
open AnalyticBridge.VerifiedReset
set_option quotPrecheck false
local notation "X" => (E.addr i).support
local notation "m"=>{(E.addr i).site}
local notation "b4"=> Healthy t X
local notation "A2"=> Healthy t ({(E.addr i).site}:Support c)
def breeze : EvenA c N:= masked t ({(E.addr i).site}:Support c) (fun _=>lampShelf E i) U -- syntax t implicit
noncomputable def branches (E:Gem c N ι)(t:ℝ): Ruby.Hue c N ι:=⟨fun i=>(E.addr i).support,fun i U=>masked t (E.addr i).support (fun _=>tallyShelf E i) U-(sewShelf E i+breeze (t:=t) E i U)⟩
lemma mask_sub (X1:Support c)(f g:Grid c→EvenA c N) : masked t X1 (f-g) U= masked t X1 f U-masked t X1 g U:=by unfold masked Set.indicator; split; rfl; exact (sub_zero _).symm
lemma golden : letters E t U i=letters (dusting E) t U i+ (sewShelf E i+breeze (t:=t) E i U)+(branches E t).mean i U:=by
    unfold branches; rw [show letters (dusting E) t U i= masked t X (E.view i-(fun _=>tallyShelf E i)) U from rfl,mask_sub]; unfold letters; let A0:=masked t X (E.view i) U; let f₀:=masked t X (fun _=>tallyShelf E i) U; let K:=(sewShelf E i+breeze (t:=t) E i U);change A0=A0-f₀+K+(f₀-K); abel
lemma inspect : (branches E t).mean i U= if Healthy t X U then 0 else -(sewShelf E i + breeze (t:=t) E i U):=by
    by_cases hh: Healthy t X U
    · have ht: A2 U:= hh.mono_left (singleton_subset_iff.mpr (E.addr i).anchor); simp only [branches,breeze,masked_eq _ _ _ _ hh,masked_eq _ _ _ _ ht,tallyShelf,if_pos hh,sub_self]
    simp only [branches,masked_ne _ _ _ _ hh,if_neg hh,zero_sub]
lemma readsL (Z:EvenA c N)(Y:Support c): UsesFinal (G:=su) t Y (masked t Y (fun _=>Z)):=by
    intro i j _ hx; unfold masked Healthy; have h: Disjoint Y (flags t i) ↔ Disjoint Y (flags t j):= by rw [disjoint_iff_inter_eq_empty,hx, ← disjoint_iff_inter_eq_empty]
    simp only [Set.indicator,Set.mem_setOf_eq,h]
lemma charges : (branches E t).Tall t:=by
    constructor
    · intro i V W he hp; refine congr_arg₂ (·-·) (readsL (c:=c) (N:=N) _ _ V W he hp) (congr_arg₂ _ rfl (Work.H03.reads_larger (show ({(E.addr i).site}:Support c)⊆(E.addr i).support from singleton_subset_iff.mpr (E.addr i).anchor) (readsL (c:=c) (N:=N) _ _ ) V W he hp)) -- X notation global may capture i earlier; inspect
    · intro i; exact (RG.masked_measurable t _ _ measurable_const).sub (measurable_const.add (RG.masked_measurable t _ _ measurable_const))
    · intro i V hg hx; exact hg ((inspect E i V).trans (if_pos hx))
    intro i V; rw [inspect]; split
    · exact Fleet.spruce _
    change Gated (E.addr i).support (- _); rw [← zero_sub]; refine wingsZ _ _ _ (Fleet.spruce _) ?_; unfold Gated; rw [map_add]; refine Subalgebra.add_mem _ (gator (E.addr i).support _) ?_; simp only [breeze,masked,Set.indicator,Set.mem_setOf_eq]; split
    · exact frameShelf E i (E.addr i).support (E.addr i).anchor
    exact Fleet.spruce _
-- no bundle of phase weights because need retain indices by (λ,s) groups
variable (h:CrossP E)(he:E.Gather)
include h he
lemma bridge (w : Equiv.Perm ι)(hp: Warrant v g k)(hf:∀ i,E.addr (w i)= rotateL (E.addr i) v ∧ ∀ U, Diode N v k g (E.view i (sky v U))= E.view (w i) U): (branches E t).bud (w i)=((branches E t).bud i).image (act v)∧ Diode N v k g ((branches E t).mean i (sky v U))=(branches E t).mean (w i) U:=by
    obtain ⟨hZ,hh⟩:= hf i; have hΩ:(E.addr (w i)).support=(E.addr i).support.image (act v):=congr_arg RegularAddress.support hZ; let X' (i:ι): Support c:={(E.addr i).site}; have hw:X' (w i)= (X' i).image (act v):=by unfold X'; rw [image_singleton,hZ]; rfl
    refine ⟨hΩ,?_⟩; change Diode _ _ _ _ (_-_) =_; unfold branches; rw [map_sub,map_add,sew_turn E i hp (fun i=>(hf i).2 1)]
    refine congr_arg₂ _ (sprayer _ _ _ _ _ _ _ _ ( hΩ.symm ▸ (healthy_image ..).symm) (transfer E i h he w k hp hf)) (congr_arg₂ (·+·) rfl (sprayer t (X' i) (X' (w i)) _ _ _ _ _ (hw.symm ▸ (healthy_image ..).symm) (turn_lamp E i hp _ hZ (h.num i 1) hh (h.gauge i) (he.role i _))))
omit he in
lemma solace : Regal c N ((branches E t).mean i U)=(branches E t).mean i U:=by
    rw [inspect]; simp only [breeze,masked,Set.indicator,Set.mem_setOf_eq]; split <;> first| exact map_zero _| skip
    split
    · unfold sewShelf; rw [map_neg,map_add,Regal_lamp E i h, Reggae.thorough ..]
    simp only [add_zero,map_neg]; unfold sewShelf; rw [Reggae.thorough ..]
omit h he
lemma phaseT : Phases ((branches E t).mean i U):=by
    intro w hw; rw [inspect]; simp only [breeze,masked,Set.indicator,Set.mem_setOf_eq]; split <;> first| exact map_zero _| skip
    split
    · unfold sewShelf; rw [map_neg,map_add,phase_lamp E i w hw, Reggae.thorough ..]
    simp only [add_zero,map_neg]; unfold sewShelf; rw [Reggae.thorough ..]
lemma gaugeT : shadeG ((branches E t).mean i):=by
    intro U k; suffices hh:sways (Lat.rotates N k) ((branches E t).mean i (gauge k U))=(branches E t).mean i U from congr_arg Subtype.val hh
    rw [inspect,inspect]; simp only [breeze,masked,Healthy,Set.indicator,Set.mem_setOf_eq,gauge_flags]; split <;> first| exact map_zero _| skip
    split
    · unfold sewShelf; rw [map_neg,map_add,gauge_lamp E, Reggae.thorough ..]
    simp only [add_zero,map_neg]; unfold sewShelf; rw [Reggae.thorough ..]
-- Tall oriented budget for any sparse.A. using tipped or widening cover equal. at height≥1 use token.
variable {v' w u U₁:ℝ}
lemma utility (h: Woven (E.addr i).site (E.addr i).support p v' (E.view i) w) (hp:0<v'): ‖token c N v' ((branches E t).mean i U)‖ ≤ (1+jointFee N)*w:=by
    have hc:=sewBudget E i h hp; have ht:= shelfBudget E i h hp; let S:=token c N v'; let R(i:EvenA c N):= S i
    have h1 : ‖S (sewShelf E i)‖≤w:= (Stem.opticX _ _ _ hp).trans (hc.sizeU 1 (AnalyticBridge.VerifiedReset.flat_ok ..)); have h2 : ‖S (lampShelf E i)‖≤jointFee N*w:= (Stem.opticX _ _ _ hp).trans (ht.sizeU 1 (flat_ok ..))
    rw [inspect E i U]; have h3 :0 ≤ jointFee N*w:=mul_nonneg (joint_valid _) h.travel
    rw [add_mul,one_mul]; split
    · rw [map_zero,norm_zero]; exact add_nonneg h.travel h3
    simp only [breeze,masked,Set.indicator,Set.mem_setOf_eq]; split
    · rw [map_neg,norm_neg,map_add]; exact (norm_add_le ..).trans (add_le_add h1 h2)
    rw [add_zero,map_neg,norm_neg]; exact h1.trans (le_add_of_nonneg_right h3)
lemma bank (w:ι→ℝ)(hp:∀ i, Woven (E.addr i).site (E.addr i).support p v' (E.view i) (w i))(hr:0 ≤ u) (hs: Shells.Warmlet.Valued E.addr (u+2) w p.B U₁) : Ac.Hit (branches E t).bud p.B (fun i=>(1+jointFee N)*w i) u (Footprint.payment 1 (4*p.B+2) 0 1 1 ((1+jointFee N)*U₁) u 0):= Stem.tipped E _ (Shells.valued_mult _ _ hs (add_nonneg zero_le_one (joint_valid _))) (fun i=> mul_nonneg (add_nonneg zero_le_one (joint_valid _)) (hp i).travel) (by linarith) hr
end Tall
end YM.QCD.Pith
#print axioms YM.QCD.Pith.Tall.bank
