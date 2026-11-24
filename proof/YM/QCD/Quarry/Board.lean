import YM.QCD.Quarry.Topography

/-! # Parameter station & pulling across Lace -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Quarry
open Function Filter Lattice Wilson Lat Stationary Precision RG Tree Tavern Revolve Push.Uniform
set_option maxHeartbeats 150000
open YM.Further.PhysicalPeriodLimitF933 Macrame Macrame.Lace Pitch
open scoped Topology Matrix Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c C f F : Side} {S : StepData c f} {M k : ℕ} (P : RG.Patch) (K : KernelChoices)
  {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val}
  (hC : C.val=c.val*M) (hc : 2≤c.val)
local notation "S₀" => stepped K h
local notation "S'" => stepped K H
local notation "L" => (Macrame.Lace.project (h:=h) (H:=H) hC hc)


abbrev Clump (n : Side):= Positions (Primary n su)
def mergeC (n : Side) : Clump n ≃L[ℝ] Cnr n:= (tint su _).trans (arm su n 1).symm
lemma input_mat (n:Side)(x : Clump n):input su n (mergeC n x)=represent (tint su _ x):=by simp only [input, mergeC, ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.apply_symm_apply]
-- default Clump coords: `Primary c` ((Site n×Typeface1)×ColorIndex)

def expandC (B : Window c C k) : Cnr c→L[ℝ] Cnr C := (mergeC C).toContinuousLinearMap ∘L (onpass (fun i:Primary C su=>((B.cut i.1.1,i.1.2),i.2))) ∘L (mergeC c).symm.toContinuousLinearMap
lemma expandsC (B : Window c C k) (x:Cnr c): input su C (expandC B x)=B.links (input su c x):=by
  obtain ⟨x,rfl⟩:=(mergeC c).surjective x; simp only [expandC,ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply,input_mat]; rfl

variable {T : Forest (decreed h)} {b : Clip} {R : PathData su} {μ B : ℝ}
variable {A : Before su μ B P.J K k} {u : Bid.Dir su c →AxisChart su T}
local notation "BU" => circuit (H:=H) hC hc T
local notation "CB" => crown (H:=H) hC hc T
variable {U : Forest (decreed H)} {v : Bid.Dir su C →AxisChart su U}
lemma purchased (hu : Critical (S:=S₀) T b R u) (hv : A.Service (S:=S') U b R v) (cb : (L).Fitted T U) (hh : Shelter (Macrame.Lace.Fitted.narrow L (G:=su)) cb.track (Push.Uniform.priced (S:=S₀) T (Lace.plain K) b R) (Push.Uniform.priced (S:=S') U (Lace.plain K) b R) (M^4)) : ∀ᶠ x : Cnr c in 𝓝 0, (encamp (S:=S') U v (expandC (L).low x)).1=(L).high.links (encamp (S:=S₀) T u x).1:=by
  have he : ∀ᶠ x : Clump c in 𝓝 0,@Push.Uniform.station su C _ S' U v (onpass (Fitted.narrow L) x)=onpass (cb).track (@Push.Uniform.station su c _ S₀ T u x):=by
    have hz:= @Enrobe.cover_germ c C f F P K h H M su hC hc T R μ B P.J k b A u U v cb (by exact hu) (by exact hv) hh
    exact hz.mono fun _ he=> he.1
  let V := (mergeC c).symm
  have ht:= he -- local abbreviations
  filter_upwards [(show Tendsto V (𝓝 0) (𝓝 0) from V.map_zero ▸ V.continuousAt.tendsto).eventually he] with x hx
  let B':= cb
  let g:= @Push.Uniform.station su c _ S₀ T u
  let y := V x
  have he := B'.governs (meetVar y (g y))
  have hi : onpass (Fitted.narrow L (G:=su)) (V x)=(mergeC C).symm (expandC (L).low x):=by
    unfold expandC; simp; rfl -- inspect
  let w := (mergeC C).symm (expandC (L).low x)
  let g':=@Push.Uniform.station su C _ S' U v
  change g' (onpass (Fitted.narrow L) y)=_ at hx; rw [show onpass (Fitted.narrow L) y=w from hi] at hx
  have hh : (meetVar y (g y) ∘ B'.bores)=meetVar w (g' w):=by
    rw [hx]; funext i; cases i <;> rw [show w=onpass (Fitted.narrow L) y from hi.symm] <;> rfl
  erw [hh] at he
  have hk {c f:Side} {S:StepData c f} {T: Forest S.ratio} {x:Cnr c} (u : Bid.Dir su c→ AxisChart su T) :
      fine su T (meetVar ((mergeC c).symm x) (Push.Uniform.station (S:=S) u ((mergeC c).symm x)))=(encamp T u x).1:=by
    unfold Push.Uniform.fine Push.Uniform.outer; rw [paint_meet (S:=S)]; unfold Push.Uniform.station; simp only [Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply]
    have hf : tint su _ ((mergeC c).symm x)=arm su c 1 x := by simp [mergeC]
    rw [hf]; rfl
  exact ((hk (S:=S') (x:=expandC (L).low x) v).symm.trans he).trans (congr_arg (fun i : Grid f=> (L).high.links i) (hk (S:=S₀) (x:=x) u))
end YM.QCD.Quarry
