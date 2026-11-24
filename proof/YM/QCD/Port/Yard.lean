import YM.QCD.Port.Plum
/-! # coordinated production independent of period and choice of kinetic. prices don't replace mixing proofs -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Tree
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra AtomF Sway OrbitG ConnectedActivityE6 Push.AbsoluteSums Footprint Jets.Touch Pressure
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {f c:Side}{F:ℕ}{u v η ξ t p C D A R z q w γ Ω π κ B:ℝ}{b m i a:ℕ}{j k:ℕ}{G:Flight j k}{J:Plan k}{H:f.val=c.val*G.L.val}{X:St f}{W:ℕ→Atom su 2} {V:Grid f}

structure CardT (L: Side)(F m b:ℕ)(C η Y:ℝ)(P:Plan j)(N:Plan k)(a b' A D σ θ ρ t e K l R X w:ℝ)(i B:ℕ)(x y p q:ℝ):Prop where
 grow : Crown P F k m L a A b' D t e K θ C i p x y q ρ
 permit : ∀ᶠ z:ℝ in atTop,
            let ξ:=haloK L z; let v:=coneK L x z; let s:=radiusB z
            let h:=highW L K θ z; let E:=coreRate L z
            ∀ (f c: Side),2*(s+1)<f.val→∀(G: Flight j k)(H:f.val=c.val*G.L.val),G.L=L→∀ (O:Offer 1 a A)(Z:Offer 2 b' D)(M:ℝ), |M|≤wink L z →
            let X₀:= park G H P O Z ξ M; let S:=sliceL G H
            |M| ≤ ξ ∧ Species G H y p v ρ q i X₀ ∧ Tow S (sun S) (sun S) X₀ ∧ Nonempty (Jets.Sun G c f H v y p ρ q i X₀) ∧ ∀ W:ℕ→Atom su 2,Iteration.Charged W σ l → Iteration.SymmetricAtoms W →
              Nonempty (Swathe G H X₀ W N y v ρ X R B)∧ ∀ Q: Swathe G H X₀ W N y v ρ X R B,RentP Q F s (fiery su z L) E h (wear L z) ∧ ∀ Φ: Varn f c→Support c, (∀ i,Φ i⊆ enlargement S b s (payT S s i)) →Ac.Hit Φ s (fun i=>Real.exp 1*shells Q F s h E i) w (betaF su z L^(-(3/8):ℝ))
lemma pops (L:Side)(x C:ℝ)(he:0<C):∀ᶠ y in atTop,wink L y≤haloK L y∧ coneK L x y≤C:=by
  have hx0 : Rate su L (-(1/32)*↑(2:ℕ)) (fun i=>coneK L x i):= Rate.mul_left (Rate.power (L:=L) (G:=su) (a:= -(1/32))|>.pow 2) x
  have hx := hx0
  have hv:=Rate.power (G:=su) (L:=L) (a:=(-(1/2))) (-(1/32)) (by norm_num)
  filter_upwards [hx.below (by norm_num) C he,hv] with i hx hi using ⟨(le_abs_self _).trans hi,(le_abs_self _).trans hx⟩
lemma dilation (P:Plan j)(N:Plan k)(F m n:ℕ)(t e K θ ρ w :ℝ)(h:0<θ)(hp:4 ≤ j)(hj:4 ≤ k)(ht:θ<1/8)(he:0 ≤e)(hz:0≤w)(hu:0 < K)(hw:0 < ρ)(hT:0<t): ∃ l:ℕ,∀ L:Side,l ≤ L.val → ∀ (a b A D ζ Ω:ℝ), 0 < a → 0 < b → 0 ≤ A→ 0 ≤ D → 0 < ζ → ∃ C R X i B x y p q, CardT L F m n C θ θ P N a b A D ζ θ ρ t e K Ω R X w i B x y p q := by
  let v:=ρ/2; let u:= v/4; have hv:0 < v:=half_pos hw; have hU:0 < u:=by unfold u; positivity
  obtain ⟨k₀,hk⟩:=apparel P F k m hp hj t e K θ ρ hT he hu h hw
  obtain ⟨k₁,h₁⟩:= Fees.exponent n hU hz (show 2*u<v from by unfold u; linarith)
  refine ⟨max k₀ k₁,fun L hL a b A D ζ Ω ha hb hA hD hΩ => ?_⟩
  obtain ⟨C,hc,i,p,x,y,q,H⟩:= hk L ((le_max_left ..).trans hL) a b A D ha hb hA hD
  obtain ⟨B,δ,X,R,hδ,hX,hR,HH⟩:= agriculture (L:=L) hw hΩ i p p Ω N; have hθ:= H.orbit
  refine ⟨C,R,X,i,B,x,y,p,q,H,?_⟩
  filter_upwards [pops L x δ hδ,H.pays,kentucky L hθ,fitsB L F B i n P N a A b D K R X θ ρ v w u p x y 0 q h ht hv (by unfold v; linarith) hθ hu] with z hv' hl hK HX
  intro ξ s t hH E f c Hf G hg hG O Z m hm X₀ S; have hp:= hm.trans hv'.1
  have hz:= (hl.2.2 f c Hf O Z m G hg hG hp).1; have hu:= paraded (P:=P) (C:=O) (D:=Z) (m:=m) G hg ha hb hK.1 hK.2.2 -- binder duplicate
  refine ⟨hp,hz,hu,sun_nonempty hz hl.2.1,fun W ht he=>?_⟩
  have he' : reserve v w (conversion S n) u:= h₁ c f S (show k₁ ≤ S.count.val from ((le_max_right ..).trans hL |>.trans_eq (show (L:ℕ)=S.count.val from congr_arg PNat.val hG.symm)))
  exact ⟨HH _ B c f G hg y q s hv'.2 hG le_rfl X₀ hz hu W ht he, HX f c Hf G hg hG he' O Z m hm hz W⟩
end YM.QCD.Port
