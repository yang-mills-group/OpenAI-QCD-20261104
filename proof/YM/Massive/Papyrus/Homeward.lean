import YM.Massive.Papyrus.Veneer
/-! # Compensation of fixed cover walks from the same Snap jets.

Matrix-valued covariants to exact truncation order (need NOT live in U(3)
after this operation). Then orient the spin sampling stencil on them. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Papyrus.Boat
open Lattice Wilson RG Source Function QCD Source.Drops UV Filter Work.G05 Finset Matrix Labels
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical
open Scan Paper
variable {H:Hol su}{d h:ℕ}(u:Flag H d h)
local notation "M" => Mat
variable (x:Cover)
lemma colour_star (u:su.El) : star (Lat.colour u)=Lat.colour u⁻¹:=rfl
lemma starcolour (u:su.El) : star (Lat.colour u)*Lat.colour u=1:=su.mat_star_mul u
lemma colourstar (u:su.El) : Lat.colour u*star (Lat.colour u)=1:=su.mat_mul_star u
lemma travel_charge (w:Walk)(U:Land): travel (night U) x w=conjugate (travel U x w):=by
   induction w generalizing x with
   | nil=> rw [travel,travel,recol_el]
   | cons a w ih=> rw [travel,travel, ih, conj_el]; unfold Step.read; split; rw [conj_rev]; rfl; rfl
/-- The raw path -/
def loomP (x:Cover)(U:Land): su.El:=travel U 0 (route 0 x 1)
def loomM (x:Cover)(U:Land): M:= Lat.colour (loomP x U)
lemma loom_gauge (k:Cover→su.El)(U:Land):loomP x (gaugeF k U)=k 0 * loomP x U*(k x)⁻¹:=by unfold loomP; rw [gaugeF,travel_gauge, route_end]
lemma loomMG (k:Cover→su.El)(U:Land):loomM x (gaugeF k U)= Lat.colour (k 0)*loomM x U *star (Lat.colour (k x)):=by rw [loomM,loom_gauge,colour_mul,colour_mul]; rfl
lemma loom_c (U:Land) : loomM x (night U)=Mstar (loomM x U):=by unfold loomM loomP; rw [travel_charge]; rfl
lemma loom_to (H:Hol su)(k:su.El)(J:Snap su h) : star (loomM x (trunkJ _ H (tinted k _ J)))= (Lat.colour k)*star (loomM x (trunkJ _ H J))*star (Lat.colour k):=by rw [panorama,loomMG,star_mul,star_mul,star_star,mul_assoc]
lemma loom_R (H:Hol su)(J:Snap su h) : star (loomM x (trunkJ _ H (recol _ J)))= Mstar (star (loomM x (trunkJ _ H J))):=by rw [Scan.spectrum,loom_c]; rfl
lemma loom_analytic (H:Hol su)(h:ℕ) : AnalyticAt ℝ (fun J : Snap su h=> loomM x (trunkJ _ H J)) 0:=(Work.G02.walkGerm H h (route 0 x 1) 0).1
lemma loom_smooth (H:Hol su)(h:ℕ): ContDiffAt ℝ (d:ℕ∞) (fun J: Snap su h=> star (loomM x (trunkJ _ H J))) 0:= ((((starL' ℝ: Mat≃L[ℝ]Mat).contDiff.comp_contDiffAt _ (loom_analytic x H h).contDiffAt)).of_le le_top) -- syntax
lemma loom_canvas : Canvas (loomM x):=patternM (fun i j=> traveling (route 0 x 1) 0 i j)
-- adjust high precision, near-root lens.Prototyp.
def adjust (x:Cover)(U:Land): M:= blockTaylor d (fun J : Snap su h=> star (loomM x (trunkJ _ H J))) (u.F U)
abbrev reshape (u:su.El)(v:su.El): M→L[ℝ] M:= (ContinuousLinearMap.mul ℝ M (Lat.colour u)).comp ((ContinuousLinearMap.mul ℝ M).flip (star (Lat.colour v)))
lemma reshape_apply (u v:su.El)(X:M) : reshape u v X= Lat.colour u*X* star (Lat.colour v):= (mul_assoc (Lat.colour u) X (star (Lat.colour v))).symm
abbrev castM (u:su.El) : M→L[ℝ] M:=reshape u u
lemma adjust_gauge(k:Cover→su.El)(U:Land): adjust u x (gaugeF k U)=reshape (k 0) (k 0) (adjust u x U):=by
   unfold adjust; rw [u.color]; refine blockTaylor_equivariant (loom_smooth x H h) (tinted (k 0) h) (reshape _ _) (Eventually.of_forall fun i=> ?_) (u.F U); rw [Function.comp_apply, Function.comp_apply]; exact (loom_to x H (k 0) i).trans (reshape_apply (k 0) (k 0) (star (loomM x (trunkJ _ H i)))).symm
lemma adjust_c (U:Land): adjust u x (night U)= Mstar (adjust u x U):=by
   unfold adjust; rw [u.shine]; exact blockTaylor_equivariant (loom_smooth x H h) (recol h) Mconj (Eventually.of_forall fun i=> loom_R x H i) (u.F U)
lemma adjust_canvas : Canvas (adjust u x):= u.tight.swing _
lemma adjust_π : Response d (fun i=>adjust u x (trunkJ h H i)) (fun i : Snap su h=> star (loomM x (trunkJ _ H i))) 0:= u.lens.transit (v':=fun i : Snap su h=> star (loomM x (trunkJ _ H i))) (Response.blocked (loom_smooth x H h))
def cabinA (x:Cover)(U:Land): M:= adjust u x U*loomM x U
lemma cabinA_gauge(k:Cover→su.El)(U:Land): cabinA u x (gaugeF k U)= reshape (k 0) (k x) (cabinA u x U):=by
   let X:=Lat.colour (k 0); let Y:=Lat.colour (k x); unfold cabinA; rw [loomMG,adjust_gauge,reshape_apply,reshape_apply]; let A:=adjust u x U; let B:=loomM x U; change X*A*star X*(X*B*star Y)=_; rw [show X*A*star X*(X*B*star Y)=X*A*(star X*X)*B*star Y by simp only [mul_assoc], starcolour, mul_one]; rw [mul_assoc X A]
lemma cabinA_R (U:Land): cabinA u x (night U)= Mstar (cabinA u x U):=by rw [cabinA,cabinA,adjust_c,loom_c,mstar_mul]
lemma cabinA_tight : Canvas (cabinA u x):= Canvas.bilin (adjust_canvas u x) (loom_canvas x) (ContinuousLinearMap.mul ℝ M)
lemma cabinA_π : Response d (fun i=>cabinA u x (trunkJ _ H i)) (fun _ : Snap su h=>1) 0:=by
   have hl:Response d (fun i=>loomM x (trunkJ h H i)) (fun i=> loomM x (trunkJ h H i)) 0:= Response.refl ((loom_analytic x H h).contDiffAt.of_le (m:=d) le_top); have he:= (adjust_π u x).product hl; simp_rw [loomM, starcolour] at he; exact he
end YM.Massive.Papyrus.Boat
#print axioms YM.Massive.Papyrus.Boat.cabinA_π
