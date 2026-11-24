import YM.QCD.Orbit.Top

/-! # transit law birth score, jet of actual rooted asymmetric tree
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Orbit
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Run Revolve Flume Sparks Quarry YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Macrame
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {c C f F m : Side}{k j N:ℕ}
lemma driver (P:Plan j)(A:Train j) (n : Side): Majestic (fun U:Grid n=>wood P 0 A U):=by
  constructor
  · intro U s d p h hs; exact spin_wood h hs A P U
  intro x; exact ((funds0 _).2 (spinO ..)).symm
lemma wood_prism (P:Plan j)(A:Train j) (S:SparkMesh):
    Clan S (fun i=>castF (n:=S.n i) (fun U=> wood P 0 A U)):=by
  obtain ⟨d,c,h,hh,H⟩:=Rudder.pays_all P
  obtain ⟨I,M,hM,H⟩:= H A
  have ht:= grove (Eyrie.trek hM) h S
  have he : (fun i=> castF (n:=S.n i) (fun U=>wood P 0 A U))=(fun i=> (metastage (queen ∘ M) (S.n i))) := by
    ext1 i; funext x; unfold metastage dust castF; simp_rw [Function.comp_apply, queen_rides]; exact (H ..).tsum_eq.symm
  rw [he]; exact ht
lemma rubber {n:Side} {x:Site n}{d:Site n→ℂ} (hp:Glare 1 0 0 x d): Quaint (parallel x) d := ⟨hp.sign,fun u v=> by rw [glared hp]; unfold affine; simp; exact Or.inl rfl⟩
lemma rubber_eq {n:Side}(x:Site n)(d : Site n→ℂ): stream (parallel x) d=hues x 1 d 1:=by
  ext ⟨i,a⟩ ⟨j,b⟩; unfold stream parallel hues rides shiftE; simp only [Matrix.of_apply, Prod.mk.injEq,Equiv.trans_apply,Equiv.apply_symm_apply]; -- inspect
  change (if i + x = j ∧ a = b then d i else 0)=if affine 1 x i=j then _ else _; by_cases he : i+x=j <;> simp [affine,he,wave_one,Matrix.one_apply]
-- not requiring connections outside larger contexts

def Blank (D : Grid f→Sheet f) := (∀ k U,D (Lattice.gauge k U)=aura (siteRot k) (D U)) ∧ Majestic D ∧ (∀ x : Site f,∀ d:Site f→ℂ,Quaint (parallel x) d→∀ U, D (pull 1 x U)*stream (parallel x) d= stream (parallel x) d* D U) ∧ D 1=0 ∧ ContDiffAt ℝ ω (castF D) 0

variable (P:Flight j k) (K:KernelChoices) (h : f.val=c.val*P.L.val)
abbrev Venue := stepped (P:=P.patch) K h
lemma ratio_align : sliceL P h=(Venue P K h).ratio:=rfl

variable {P K h} {M : PathData su} {p : Clip} {H:Forest (Venue P K h).ratio} {u : Bid.Dir su c→AxisChart su H}
  {g a C Λ : ℝ} (hu: Critical (S:=Venue P K h) H p M u) (he : Bid.Larger (G:=su) (Venue P K h))(hh: M.Bounds p a C Λ) (hv: PriceGap (S:=Venue P K h) H p M g)(hg:0<g)
  (B: Plan j) {D : Grid f→Sheet f}(hD : Blank D)
local notation "Δ" => shiftL P h B D
local notation "r" => (sliceL P h)
include hu he hh B hv hD hg

lemma conduct (hs:ContDiffAt ℝ ω (mirage H Δ u) 0): Priest (mirage H Δ u) ∧ Noble (mirage H Δ u):=by
  let X:= Venue P K h; have ha : Rooted X Δ:=fun k p=> shiftK P B h D (fun _ p=> hD.1 p _) _ k
  let v : X.Choices := Classical.arbitrary _
  refine ⟨⟨hs,?_,Quarry.static hu v he.1 hh hv hg ha,Quarry.trek hu v he.1 hh hv hg ha⟩,⟨?_,?_⟩⟩
  · intro x; obtain ⟨d,hd⟩:= shades 1 0 0 ((r).embed x)
    let k:= d ∘ (r).embed; let V:= hues x 1 k 1
    have ht': (r).embed (0:Site c)=0:=map_zero (r).root
    have HH': Glare 1 0 0 x k:= shrouds r (a:=0) (y:=0) (b:=x) (by rw [ht']; exact hd)
    have hp := rubber hd; have hx : V∈unitary _:=colour_wheel HH' Swing.none
    have hW U:=hD.2.2.1 _ d hp U
    have hF U: D (pull 1 ((r).embed x) U)= aura (hues ((r).embed x) 1 d 1) (D U):=by
      have hP:= hW U; rw [rubber_eq] at hP; unfold aura; rw [← hP, Matrix.mul_assoc,(colour_wheel hd Swing.none).2,mul_one]
    have hx' U : Δ (pull 1 (X.ratio.embed x) U)=aura V (Δ U):=orientK P B h D U x hd Swing.none (hF U)
    refine ⟨k,rubber HH',?_⟩; filter_upwards [orbit_space hu v he.1 hh hv hg ha x k hx'] with y H₀
    rw [rubber_eq,H₀]; unfold aura; change _ * star V * V = _; rw [Matrix.mul_assoc _ (star V),hx.1,mul_one]
  · intro s
    have ht' : (r).embed (0:Site c)=0:=map_zero (r).root
    let x : Site c:=0; let T:=starTraffic s; let p:=gem s f; let K:=p ∘ (r).embed
    have hp:Glare s 0 0 ((r).embed x) p:=by unfold x; rw [ht']; exact gems ..
    have hs:= fleetLeft s
    have hV (U:Grid f): Δ (pull s 0 U)= aura (hues x s K T) (Δ U):=by
      have ht (U:Grid f): D (pull s ((r).embed x) U)=aura (hues ((r).embed x) s p T) (D U):=by unfold x; rw [ht']; exact hD.2.1.port _ s p T (gems ..) hs
      have he:=orientK P B h D U x hp hs (ht U); unfold x at *; rw [ht'] at he; exact he
    have Ht : Glare s 0 0 (0:Site c) K:= shrouds r (a:=0) (y:=0) (b:=0) (by rw [ht']; exact gems ..)
    filter_upwards [Quarry.orbit_compass hu v he.1 hh hv hg ha s K T hV] with z H'
    apply Eq.trans H'
    let A:=hues (0:Site c) s K T; let V:=scaleA s c; let Z:= mirage H Δ u z
    have he : star A∈ unitary _:= Unitary.star_mem (colour_wheel Ht hs)
    have hp:=compass_eq Ht hs (aura A Z); rw [compatible _ _ (colour_wheel Ht hs)] at hp -- maybe A def
    change aura A Z=aura V Z; nth_rw 2 [hp]; rw [inverse_aura (B:=V) _ (colour_wheel (gems s c) hs)]
  exact Eventually.of_forall fun x=> (newborn_s P B h _ (hD.2.1.lane _).symm).symm
end YM.QCD.Orbit
