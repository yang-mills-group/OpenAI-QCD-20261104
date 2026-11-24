import YM.QCD.Spice.Castle
import YM.QCD.Dust.Quote
/-! # Prices for ψ comparison operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Spice
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Jets
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun Cove.Fj Jets.Touch MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w t b':ℝ}{l b:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "D₀"=> Junta c f F
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)
open Dust Stew Brick Garden
variable {σ ζ K D μ B₀ m :ℝ}
section data
variable {X: Grid f→Sheet f} {R:Ratio c f}
-- Note gets optic_spatial Lagrange. comparisons use triangle. orientation (separation target, source head).
variable {f1 f2:Water c f F}{i: Keys f F}
abbrev amount (f':Water c f F)(i: Keys f F) (R:Ratio c f):= ∑ j:Keys c F,Fork.meets R (locationP i) 2 (locationP j)*‖f' i j‖
lemma pour (h: amount f1 i R≤ K)(hy:0 ≤ y): Stew.plank (R.parent (locationP i)) y (changeVars f1 (atom i)) ≤ K*y:=by
    unfold Stew.plank; rw [change_atom]; apply (vc_sum ..).trans; apply le_trans _ (mul_le_mul_of_nonneg_right h hy)
    unfold amount; rw [sum_mul]; apply sum_le_sum; intro j hj; rw [vc_scale,reachA j hy,Fork.meets]; unfold Stew.lens; rw [separation_comm]; exact le_of_eq (by ring)
lemma billows (h: amount f1 i R≤ K)(ht:4*(K*y)≤x)(hv:0<y)(o:Site f):
    dryL y (changeVars f1 (atom i)) ≤ x ∧ Stew.plank (R.parent o) y (changeVars f1 (atom i))≤(1+(Stew.lens o i:ℝ))^2*x:=by
    let k:=locationP i; let X:=changeVars f1 (atom i); let r:=R.parent k
    have hp := pour h hv.le; have hh: 0≤ K*y:=(norm_nonneg _).trans hp; have he :K*y≤x:=(show _≤4*(K*y) by linarith).trans ht
    refine ⟨((shot (Stew.lens r) X y hv).trans (hp.trans he)), ?_⟩ -- syntax
    apply (trails (R.parent o) r X hv.le).trans
    have h':(1+(separation r (R.parent o):ℝ))^2 ≤4*(1+(Stew.lens o i:ℝ))^2:=by
       apply (pow_le_pow_left₀ (by positivity : 0 ≤ (1+(separation r (R.parent o):ℝ))) (show (1+(separation r (R.parent o):ℝ))≤ 2*(1+(separation k o:ℝ)) from ?_) 2).trans; rotate_left
       · have hf: (separation r (R.parent o):ℝ) ≤ separation k o + 1:=by exact_mod_cast YM.Work.E04.parent_separation R k o
         linarith only [hf,Nat.cast_nonneg (α:=ℝ) (separation k o)]
       exact le_of_eq (by unfold k Stew.lens; ring)
    exact (mul_le_mul h' hp (norm_nonneg _) (by positivity)).trans ((le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left ht (show 0≤(1+(Stew.lens (N:=F) o i:ℝ))^2 by positivity))) -- inspect lens ambiguous
lemma rimDiff (i:Keys f F) (f1 f2: Water c f F): changeVars f1 (atom i)-changeVars f2 (atom i)=changeVars (f1-f2) (atom i):=by rw [change_atom,change_atom,change_atom,← sum_sub_distrib]; exact sum_congr rfl fun j _=> (sub_smul ..).symm
lemma souvenir (hF:amount f1 i R ≤ K)(hA:amount (f1-f2) i R≤ σ): amount f2 i R ≤ K+σ:=by
    apply le_trans _ (add_le_add hF hA); unfold amount; rw [← sum_add_distrib]; refine sum_le_sum fun j _=>?_ ; rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ (meets_nn ..); apply le_trans (norm_le_insert f1 f2 i j); rfl
where norm_le_insert (p p':Water c f F)(i j) : ‖p' i j‖ ≤ ‖p i j‖+‖(p-p') i j‖:=by simpa [Matrix.sub_apply, dist_eq_norm,add_comm] using norm_sub_le_norm_sub_add_norm_sub (0:ℂ) (p i j) (p' i j)
lemma echo (S':Ratio c f)(T:Water c f F) (P:Fields f F): wipe A B T (near A B P)= changeVars T P:=by
    have hm:(wipe A B T).comp (near A B)=changeVars T:=by
       apply ext_atoms; intro i; rw [AlgHom.comp_apply]; rw [show near A B (atom i)=atom (head A B i) from embed_atom _ _,wiper,change_atom]
    exact congr_arg (fun F=>DFunLike.coe F P) hm -- universe
end data
variable {P₀:Plan j} {r A₀ A₁ d:ℝ} {U:Offer 1 σ K}{V:Offer 2 ζ A₁}
local notation "T!"=>fun m :ℝ=>pesto P₀ G h (trunkM U V d m f)
section warmth
variable (H:Sun G c f h δ v q u a l (pesto P₀ G h (trunkM U V d m f)))(H':Sun G c f h δ v q u a l (pesto P₀ G h (trunkM U V d 0 f))) (o: Keys f F)(X:Grid f)
variable (hx:beamAt (trunkFt (locationP o) b) X 1 w)(ht:w<δ/2)(hv:∀ n:ℕ,(1+(n:ℝ))^2 ≤ η*Real.exp (u/2*n))(hp:0 ≤ w)(he:0<u)(hd:0 ≤ η)
include hx ht hv hp he H' hd
lemma blueberry : amount ((H.equip F b).shortP X-powerF (proton G h)) o (sliceL G h) ≤ fingers F*soil P₀ G.L b l u δ w η q |m| a 2:=by
    let X' x i:=spoon H.Z x b x i (settled X)-cell (proton G h) x i; let Y i x:=spoon H.V x b i x (settled X)-cell (barP G h) i x
    have hP : (H.equip F b).shortP X-powerF (proton G h) = foamB X' Y:=by
      ext i j; change short H.Z H.V b (settled X) i j-powerF _ _ _=_; rw [show powerF (N:=F) (proton G h)= foamB (cell (proton G h)) (cell (barP G h)) from ?_]; swap; · rw [rotateP P₀]; rfl
      rcases i with i|i <;> rcases j with j|j <;> simp only [short,foamI,foamR,foamRL,foamLR,Y,X'] <;> first| exact sub_zero _| split <;> simp -- careful
    rw [hP]; exact foamSales X' Y o _ 2 (banks H H' b 2 (locationP o) X hx ht hv hp he hd)
end warmth
variable {f':Water c f F}
lemma petals (U:Support f)(o:Site f)(Z:Crate f F) (h₀:Z∈region (limits (F:=F) U)) -- F new
    {p:Water c f F} (he: ∀ i∈limits U,amount p i (sliceL G h)≤q)(hv:0<y)(ht:4*(q*y) ≤ x/4)(hx:0<x):
    Stew.plank ((sliceL G h).parent o) y (changeVars p Z) ≤ Stew.plank o x Z:=by
     -- use data for sprinkles at p h.
     have hu: 0 ≤ x/4:=by linarith
     have hk i (hi:i∈limits (F:=F) U):= billows (he i hi) ht hv o
     apply le_trans (sprinkles (f:=Stew.lens _) hv hu (changeVars p) _ hk Z h₀ (fun _ (hi:_< (0:ℕ))=>by omega) (show 2*(x/4)=_ from (by ring: 2*(x/4)=1/2*x)) (by norm_num: (0:ℝ)≤1/2) (by norm_num) hx.le)
     rw [pow_zero,one_mul]
-- Ω.Head measure bound IMM corpus; inputs already satisfy TREE since Coat.Sha. For K.FULL pollen.g.
variable (H:Sun G c f h δ v q u a l (pesto P₀ G h (trunkM U V d m f)))(H':Sun G c f h δ v q u a l (pesto P₀ G h (trunkM U V d 0 f))) (o:Site f)(X:Grid f)(A_:Support f)
variable {β τ:ℝ} (h₁:0<x)(h₂:0<y)(hx:beamAt (halo (b+1) A_) X 1 w)(hh:Healthy t (halo (b+1) A_) X)(hG: Sea G h b δ B₀ q t H.Z H.V 2)
variable (ht:w<δ/2)(hv:∀ n:ℕ,(1+(n:ℝ))^2 ≤ η*Real.exp (u/2*n))(hp:0 ≤ w)(he:0<u)(hd:0 ≤ η)
include hx hh hG ht hv hp he hd H' h₁ h₂
lemma humming (H₀:0≤B₀)(hq:fingers F*soil P₀ G.L b l u δ w η q |m| a 2 ≤ τ) (hτ:0≤τ)(HΔ:4*(τ*y) ≤ β*(x/4))(hw:0≤β)(ht':4*((fingers F* B₀+τ)*y)≤x/4)
    (X₁: Crate f F)(hf:X₁∈ region (limits A_)): Stew.plank ((sliceL G h).parent o) y (changeVars ((H.equip F b).shortP X) X₁-apple (proton G h) F X₁) ≤ β*Stew.plank o x X₁:=by
    let M: Water c f F:= (H.equip F b).shortP X; let L:=powerF (N:=F) (proton G h)
    have hm (i:Keys f F)(hi:i∈limits A_): halo (b+1) {locationP i} ⊆ halo (b+1) A_:= Corona.halo_mono (le_refl _) (singleton_subset_iff.mpr (mem_filter.mp hi).2)
    have ha (i:Keys f F)(hi:i∈limits A_): amount M i S ≤ (fingers F*B₀):= freezeQ H i X b 2 B₀ hG (hh.mono_left (hm i hi))
    have hb (i: Keys f F)(hi:i∈limits A_):amount (M-L) i S ≤ τ:= (blueberry H H' i X (mores hx ((Corona.halo_mono (show b ≤ b+1 from by omega) (Subset.refl {locationP i})).trans (hm i hi))) ht hv hp he hd).trans hq
    let f':= changeVars M; let e:= changeVars L
    have hu: 0 ≤ x/4:=by positivity
    have hR (i:Keys f F)(hi:i∈limits A_):= billows ((ha i hi).trans (le_add_of_nonneg_right hτ)) ht' h₂ o; have hk (i:Keys f F)(hi:i∈limits A_):= billows (souvenir (ha i hi) (hb i hi)) ht' h₂ o
    apply (rind f' e h₂ hu hR hk ?_ hw X₁ hf).trans_eq ?_; rotate_left
    · rw [show 4*(x/4)=x by ring]
    intro i hi; unfold f' e; rw [rimDiff]; exact billows (hb i hi) HΔ h₂ o
end YM.QCD.Spice
