import YM.QCD.Dust.Rose
/-! # entire operator estimates in scaled two different weights. Lag cost inherited across FULL fit. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Dust
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Brick
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent Reggae
open PhysicalNext.JointLoad MultiNext.SignedSource
variable {c f L:Side} {j k N n:ℕ} {C h1 h2 u v w t:ℝ} {o:Site f}{r:ℝ}
local notation "A"=> Crate f N
local notation "X" => Keys f N
-- general coordinate transport. Entire on Complex
abbrev Rune (f:Side):= (Site f→Bundle) × (Site f→Bundle)
def ramp (f:Side)(k:Frame f): Rune f := (fun i=>Lat.touch (colour (k i)),fun i=>Lat.touch (colour ((k i)⁻¹))) -- inverse notation on Mat maybe ! use star
noncomputable def tor (Y:Rune f): Matrix (Keys f N) (Keys f N) ℂ:= Matrix.fromBlocks (copies N (rides (Equiv.refl _) Y.1)) 0 0 (copies N (rides (Equiv.refl _) Y.2))ᵀ
lemma pendulum (k:Frame f) (x:EvenA f N): changeVars (tor (ramp f k)) x.val=(sways (rotates N k) x).val:=by
    suffices h: copies N (rides (Equiv.refl _) (ramp f k).2)=star (Lat.rotates N k) by unfold tor; rw [h]; rfl
    unfold Lat.rotates; rw [← copies_star,siteRot_star]; rfl
lemma ravine (Y:Rune f)(i j:X): locationP i ≠locationP j → tor Y i j=0 :=by
   intro hp; rcases i with ⟨⟨x,i⟩,b⟩|⟨⟨x,i⟩,b⟩ <;> rcases j with ⟨⟨y,j⟩,a⟩|⟨⟨y,j⟩,a⟩
   · change (copies N (rides (Equiv.refl _) Y.1)) ((x,i),b) ((y,j),a)=0; have hh:x≠y:= hp; rw [copies,Matrix.blockDiagonal_apply]; split; exact if_neg hh; rfl
   · exact rfl
   · exact rfl
   change (copies N (rides (Equiv.refl _) Y.2)) ((y,j),a) ((x,i),b)=0; have hh:y≠ x:=(show x ≠ y from hp).symm; rw [copies,Matrix.blockDiagonal_apply]; split; exact if_neg hh; rfl
lemma cremate (Y:Rune f)(i j:X): ‖tor Y i j‖≤‖Y‖:=by
   have hh (Z:Site f→Bundle)(hz: ‖Z‖ ≤ ‖Y‖)(i j:Modes f N): ‖copies N (rides (Equiv.refl _) Z) i j‖≤ ‖Y‖:=by
       unfold copies; rw [Matrix.blockDiagonal_apply]; simp only [rides,Matrix.of_apply]; split
       next h=> split
                next hx=> exact (Cost.north (Z _) _ _).trans ((norm_le_pi_norm Z _).trans hz)
                next h'=> exact norm_zero.le.trans (norm_nonneg _)
       next=> exact norm_zero.le.trans (norm_nonneg _)
   rcases i with i|i<;> rcases j with j|j; exact hh Y.1 (norm_fst_le _) _ _; exact norm_zero.le.trans (norm_nonneg _); exact norm_zero.le.trans (norm_nonneg _); exact hh Y.2 (norm_snd_le _) _ _
lemma torch (i j:X): ContDiff ℂ ω (fun Y:Rune f=>tor Y i j):=by
    have H(Z:Rune f→Site f→Bundle)(hp:ContDiff ℂ ω Z)(i j:Modes f N):ContDiff ℂ ω (fun Y=> copies N (rides (Equiv.refl _) (Z Y)) i j):=by
       unfold copies; simp_rw [Matrix.blockDiagonal_apply]; split; swap; exact contDiff_const
       simp only [rides,Matrix.of_apply]; dsimp; split; swap; exact contDiff_const
       let x:= i.1; let L:Bundle→L[ℂ]ℂ:= LinearMap.toContinuousLinearMap { toFun:=fun p=>p x.2 j.1.2,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
       exact L.contDiff.comp (f:=fun Y=>Z Y x.1) ((ContinuousLinearMap.proj (φ:=fun _ : Site f=>Bundle) (R:=ℂ) x.1).contDiff.comp hp) -- name
    rcases i with i|i<;> rcases j with j|j; exact H Prod.fst contDiff_fst i j; exact contDiff_const; exact contDiff_const; exact H Prod.snd contDiff_snd j i
lemma leapX (s:Site f): ((limits (F:=N) {s}).card:ℝ)=stemF N:=by rw [limits_card, card_singleton]; push_cast; unfold stemF Jets.Sun.fingers; ring
lemma monument (Y:Rune f)(i:X)(hp: ‖Y‖≤v)(ht:0<t): dryL t (changeVars (tor Y) (atom i))≤ stemF N*(v*t) ∧ visc (Stew.lens o) t (changeVars (tor Y) (atom i))≤(1+(Stew.lens o i:ℝ))^2*(stemF N*(v*t)):=by
   rw [change_atom]
   let S:= limits (F:=N) ({locationP i}); rw [← sum_subset (s₁:=S) (subset_univ S) (fun j _ h=>?_)]
   swap
   · rw [ravine _ _ _ (fun k=> h (show j∈limits (F:=N) {locationP i} from mem_filter.mpr ⟨mem_univ _,mem_singleton.mpr k.symm⟩)),zero_smul]
   constructor
   · have h:= ht
     apply (load_sum ..).trans; simp_rw [load_scale]; apply (sum_le_sum (g:=fun _=> v*t) (fun j _=> ?_)).trans_eq; · simp only [sum_const,nsmul_eq_mul,S,leapX]
     rw [load_atom _ (fun _=>h)]; exact mul_le_mul_of_nonneg_right ((cremate ..).trans hp) ht.le
   apply (vc_sum ..).trans; simp_rw [vc_scale]; apply (sum_le_sum (g:=fun _=> v*((1+(Stew.lens o i:ℝ))^2*t)) (fun j hj=> ?_)).trans_eq
   · simp only [sum_const,nsmul_eq_mul,S, leapX]; ring
   rw [reachA j ht.le,show Stew.lens o j=Stew.lens o i from congr_arg (fun x=>separation x o) (mem_singleton.mp (mem_filter.mp hj).2)]
   exact mul_le_mul_of_nonneg_right ((cremate ..).trans hp) (by positivity)
abbrev fareG (v t:ℝ)(N:ℕ):ℝ:=2*(v*(1+stemF N))*t
lemma stems (Y:Rune f)(hp: ‖Y‖ ≤v)(hv:0< v)(ht:0<t)(he:fareG v t N≤r) (Z:Crate f N): visc (Stew.lens o) t (changeVars (tor Y) Z) ≤ visc (Stew.lens o) r Z:=by
    let g:= v*(1+stemF N); have hs:0 ≤ stemF N :=by unfold stemF Jets.Sun.fingers; positivity
    have hg:0 ≤ g :=by unfold g; positivity
    have hp (i:Keys f N):stemF N*(v*t) ≤ g*t:=calc
       _ ≤ (1+stemF N)*(v*t):=by gcongr; linarith
       _ = _:=by unfold g; ring
    have hq i : dryL t (changeVars (tor Y) (atom (i:Keys f N))) ≤ g*t ∧ visc (Stew.lens o) t (changeVars (tor Y) (atom i)) ≤ (1+(Stew.lens o i:ℝ))^2*(g*t):=by
       obtain ⟨h,hx⟩:= monument (o:=o) Y i (by assumption) ht
       exact ⟨h.trans (hp i),hx.trans (mul_le_mul_of_nonneg_left (hp i) (sq_nonneg _))⟩
    have hf :0≤ 2*(g*t):=by positivity
    have h:= sprinkles ht (mul_nonneg hg ht.le) (changeVars (tor Y)) univ (fun i _=> hq i) Z (regio Z) (fun i (hi:i.card<0)=>by omega) (show 2*(g*t)=1*(2*(g*t)) from (one_mul _).symm) zero_le_one le_rfl hf
    simp only [pow_zero,one_mul] at h; exact h.trans (future _ hf ((mul_assoc 2 g t).symm.trans_le he) Z)
end YM.QCD.Dust
