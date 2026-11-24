import YM.Poised.Horns
import YM.Poised.Furls
/-!
# All powers thru THIS hearth.Seat BEFORE-L waits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Spice
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Jets
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun Cove.Fj Jets.Touch MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v η ξ x y w t b':ℝ}{l b:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "R"=> Junta c f F
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)
open Dust Stew Brick Garden Sway OrbitG Revolve
variable {σ σ' ζ K D μ B₀ m τ γ Λ Λ' :ℝ}
open Massive.Poised Massive.Poised.Pipes
variable {P₀:Plan j} {r A₀ A₁ d:ℝ} {U:Offer 1 σ K}{V:Offer 2 ζ A₁}
variable (H:Sun G c f h δ v q u a l (pesto P₀ G h (trunkM U V d m f)))(H':Sun G c f h δ v q u a l (pesto P₀ G h (trunkM U V d 0 f))) (o: Keys f F)(X:Grid f)
variable {nH:ℕ} (hx:beamAt (trunkFt (locationP o) b) X 1 w)(ht:w<δ/2)(hv:∀ n:ℕ,(1+(n:ℝ))^nH ≤ η*Real.exp (u/2*n))(hp:0 ≤ w)(he:0<u)(hd:0 ≤ η)
include hx ht hv hp he H' hd
lemma miramid : ∑ i:Keys c F,Fork.meets (sliceL G h) (locationP o) nH (locationP i)*‖((H.equip F b).shortP X-powerF (proton G h):Water c f F) o i‖ ≤ fingers F*soil P₀ G.L b l u δ w η q |m| a nH:=by
    let X' x i:=spoon H.Z x b x i (settled X)-cell (proton G h) x i; let Y i x:=spoon H.V x b i x (settled X)-cell (barP G h) i x
    have hP : (H.equip F b).shortP X-powerF (proton G h) = foamB X' Y:=by
      ext i j; change short H.Z H.V b (settled X) i j-powerF _ _ _=_; rw [show powerF (N:=F) (proton G h)= foamB (cell (proton G h)) (cell (barP G h)) from ?_]; swap; · rw [rotateP P₀]; rfl
      rcases i with i|i <;> rcases j with j|j <;> simp only [short,foamI,foamR,foamRL,foamLR,Y,X'] <;> first| exact sub_zero _| split <;> simp -- careful
    rw [hP]; exact foamSales X' Y o _ nH (banks H H' b nH (locationP o) X hx ht hv hp he hd)
omit H' hx ht hv hp he hd
variable {Z:Support f} {r₄:ℕ}
lemma paths_b (V: Grid f)(hH:Sea G h b δ γ q t P.Z P.V r₄)(hv:Healthy t (halo (b+1) Z) V): Stanch Z (sliceL G h) ((P.equip 6 b).shortP V) r₄ (fingers 6*γ):=fun i hi=> freezeQ P i V b _ γ hH (hv.mono_left (Corona.halo_mono le_rfl (singleton_subset_iff.mpr ((mem_filter.mp hi).2)))) -- r₄ var
include H' in
lemma canvass (hx:beamAt (halo (b+1) Z) X 1 w)(ht:w<δ/2)(hw:0≤w)(hu:0<u)(hz:∀ n:ℕ,(1+(n:ℝ))^nH≤ η*Real.exp (u/2*n))(hη:0≤η): Stanch Z (sliceL G h) ((H.equip 6 b).shortP X - powerF (proton G h)) nH (fingers 6*soil P₀ G.L b l u δ w η q |m| a nH):=by
   intro i hi; let v:=locationP i; have he : trunkFt v b⊆halo (b+1) Z:= Corona.halo_mono (Nat.le_succ _) (Finset.singleton_subset_iff.mpr (mem_filter.mp hi).2)
   exact miramid H H' i X (mores hx he) ht hz hw hu hη
-- for nonshort Mass or not.
def ambit (b:ℕ)(u₀:ℕ):ℝ:= (1+(b+1:ℝ))^u₀
lemma myths(p:ℕ)(b:ℕ): 0≤ambit p b:=by unfold ambit; positivity
lemma scrolls (U V:Grid f)(hx:beamAt (halo (b+1) Z) U V w)(ht:w<δ/2)(hw:0≤w)(hu:0≤u)(k:ℕ): Stanch Z (sliceL G h) ((P.equip 6 b).shortP U-(P.equip 6 b).shortP V) k (ambit b k*(fingers 6*q*(w/(δ/2)))):=by
    intro i hi; let T:= P.equip 6 b; let X:= locationP i; let R' := sliceL G h
    have he:trunkFt X b⊆halo (b+1) Z:= Corona.halo_mono (Nat.le_succ _) (Finset.singleton_subset_iff.mpr (mem_filter.mp hi).2)
    let L(j:Keys c 6):= T.shortP U i j-T.shortP V i j
    apply le_trans _ (mul_le_mul_of_nonneg_left (show ∑ j:Keys c 6, ‖L j‖ ≤ _ from talks P U V i hu (mores hx he) ht hw) (myths b k)); rw [mul_sum]
    apply sum_le_sum; intro j _; change (_*‖L j‖ ≤ _); by_cases hL:L j=0; · rw [hL,norm_zero,mul_zero,mul_zero]
    have hs : ∃ W,T.shortP W i j≠0 :=by by_contra! h; unfold L at hL; rw [h U,h V,sub_zero] at hL; contradiction
    obtain ⟨W,hW⟩:=hs; have hY:R'.embed (locationP j)∈halo T.trim {X}:= T.sleeps i j W hW
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply pow_le_pow_left₀ (by positivity)
    let Y:=locationP j; have hv : separation (R'.parent X) Y ≤ b+1:=by
        obtain ⟨v,hv,ht⟩:= halo_spec.mp hY; rw [mem_singleton.mp hv] at ht
        have hp : separation (R'.parent X) (R'.parent (R'.embed Y))≤ _:=YM.Work.E04.parent_separation R' _ _; rw [R'.embed_parent] at hp; exact hp.trans (Nat.add_le_add_right ht 1) -- sep orientation
    change 1+(separation (R'.parent X) Y:ℝ) ≤ 1+((b:ℝ)+1); exact_mod_cast Nat.add_le_add_left hv 1
end YM.QCD.Spice
