import YM.QCD.Quarry.Board

/-!
# odd period test with F score coherence. Can test before Hess station is
computed that each path family suffices; order-dependent claims later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Quarry
open Function Filter Lattice Wilson Lat Stationary Precision RG Tree Tavern Revolve Push.Uniform
open YM.Further.PhysicalPeriodLimitF933 Macrame Macrame.Lace Kit
set_option maxHeartbeats 40000
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c C f F : Side} {M k : ℕ} (P : RG.Patch) (K : KernelChoices)
  {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val}
  (hC : C.val=c.val*M) (hc : 2≤c.val)
local notation "S₀" => stepped K h
local notation "S'" => stepped K H
local notation "L" => (Macrame.Lace.project (h:=h) (H:=H) hC hc)
variable {T : Forest (decreed h)} {b : Clip} {R : PathData su} {μ B Λ : ℝ}
variable {A : Before su μ B P.J K k} {u : Bid.Dir su c →AxisChart su T}
local notation "BU" => circuit (H:=H) hC hc T
local notation "CB" => crown (H:=H) hC hc T
variable {W : Forest (decreed H)} {w : Bid.Dir su C →AxisChart su W}

-- introduce big repeated with propositional glue, keep explicit args
lemma doors (hu : Critical (S:=S₀) T b R u) (hR : R.Bounds b μ B Λ) (hJ : Bid.Larger (G:=su) S') {E : Forest (decreed H)} (hs : E=BU) :
    ∃ v : Bid.Dir su C→AxisChart su E, Critical (S:=S') E b R v ∧
      ∀ᶠ x : Cnr c in 𝓝 0,(encamp (S:=S') E v (expandC (L).low x)).1=(L).high.links (encamp (S:=S₀) T u x).1:=by
  let D:= Classical.choice (pre_order su μ B P.J K (show 3≤4 by decide))
  obtain ⟨v,hv⟩:= Before.graph (S:=S') E D hR hJ rfl rfl -- inspect
  refine ⟨v, Before.Service.critical hv,?_⟩
  -- produce fitted hx prior transport.
  let CB' : (L).Fitted T E := hs.symm ▸ CB
  apply purchased P K hC hc hu hv CB'
  clear v hv -- order?
  subst E
  exact Enrobe.assesses K hC hc T b R

variable {G : Grid f→Sheet c} {J : Grid F→Sheet C}
lemma faceted (hu : Critical (S:=S₀) T b R u) (hw : Critical (S:=S') W b R w) (hR : R.Bounds b μ B Λ) (hJ : Bid.Larger (G:=su) S') (he : Rooted S' J)
    (d : Site C→ℂ)
    (hz : ∀ (Z : Link su c → Grid f), Stationary.Army Z 0 → Z 0=1→∀ᶠ x in 𝓝 0, J ((L).high.links (Z x))*stream (L).low d=stream (L).low d*G (Z x)):
    ∀ᶠ x : Cnr c in 𝓝 0,mirage (S:=S') W J w (expandC (L).low x)*stream (L).low d=stream (L).low d * mirage (S:=S₀) T G u x:=by
  choose v hv Hq using doors P K hC hc hu hR hJ (H:=H) rfl
  let D:= Classical.choice (pre_order su μ B P.J K (show 3≤4 by decide))
  let t : (S').Choices := Classical.arbitrary _
  obtain ⟨hF,p0,-⟩:= D.full_pack (S:=S') W t hR hJ rfl rfl
  have hQ:= @panorama C F S' W (circuit (H:=H) hC hc T) b R _ μ B Λ w v hw t hJ.1 hR hF p0 J he hv
  let E:=expandC (L).low
  let Z (x : Link su c):= (encamp (S:=S₀) T u x).1
  have hP:=hz Z (camp_thaw hu).1 (by unfold Z; rw [encamp_zero hu]; rfl)
  filter_upwards [Hq,hP,(show Tendsto E (𝓝 0) (𝓝 0) from E.map_zero ▸ E.continuous.continuousAt.tendsto).eventually hQ] with x hk hp hh
  change mirage (S:=S') W J w (E x)*stream _ d=_
  rw [hh,mirage,show (encamp _ _ (E x)).1=(L).high.links (Z x) from hk]
  exact hp
end YM.QCD.Quarry
