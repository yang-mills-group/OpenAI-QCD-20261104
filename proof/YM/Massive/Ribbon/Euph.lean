import YM.Massive.Ribbon.Grow
import YM.QCD.Door.Twig
/-!
# Spin jets, Pin action on off-shell polynomial label space
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV
open Function Matrix Finset
open QCD QCD.Lat Lattice Grass TensorProduct
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ComplexOrder TensorProduct Kronecker Classical
variable {d : ℕ}(p q:EuPin)
local notation "Ω" => Multi d × Lat.Fiber
local notation "T" => SpinMode d
noncomputable abbrev ringK (u : T):= spinWeight u.1.1
/-- `Hue` spin action, same for all flavors. -/
lemma ribbon (p:EuPin)(X:Bundle): UV.turned (d:=d) p X= Kit.choir 6 (trM d p ⊗ₖ X):=by
    ext ⟨i,a⟩ ⟨j,b⟩; rw [Kit.choir, Matrix.blockDiagonal_apply]; unfold UV.turned; simp
lemma reel (X Y:Bundle): UV.turned (d:=d) q X* UV.turned p Y= UV.turned (p*q) (X*Y):=by
    simp_rw [ribbon, ←Kit.choir_mul, ←Matrix.mul_kronecker_mul, row_table]
lemma cool : UV.turned (d:=d) 1 1=1:=by rw [ribbon,row_id,Matrix.one_kronecker_one, Kit.replicas, Lat.copies_one]
lemma trails (X:Bundle)(i j:T)(h:ringK i≠ringK j): UV.turned p X i j=0:=by
    unfold UV.turned; rw [Matrix.of_apply]; split
    · have hf: multiMove p i.1.1 j.1.1=0:= not_ne_iff.mp (fun hv=>h (by unfold ringK spinWeight; rw [invariant_level _ _ _ hv])); rw [hf,zero_mul]
    rfl
lemma groom (u: su.El) : colorTable (d:=d) u= UV.turned 1 (touch (colour u)):=by rw [ribbon,row_id]; ext ⟨⟨i,w⟩,a⟩ ⟨⟨j,z⟩,b⟩; by_cases he:a=b <;> by_cases hv:i=j <;> simp [colorTable,Kit.choir,Matrix.blockDiagonal_apply,he,hv]
lemma alcohol (u: su.El) : (star (colorTable (d:=d) u)).transpose=UV.turned 1 (star (touch (colour u))).transpose:=by rw [groom,ribbon,ribbon, row_id]; ext ⟨⟨i,w⟩,a⟩ ⟨⟨j,z⟩,b⟩; rcases eq_or_ne a b with he|he <;> by_cases hv:i=j <;> simp [Kit.choir,Matrix.blockDiagonal_apply, he,hv, Matrix.star_eq_conjTranspose]; aesop
lemma wave_tr (X:Spike): wave X.transpose= (wave X).transpose:=by ext ⟨i,a⟩ ⟨j,b⟩; simp [wave, Matrix.one_apply, eq_comm]
lemma inter_opp (X: Mat)(p: Spike): Commute (star (touch X)).transpose (wave p.transpose):=by
    rw [touch_star,wave_tr]; unfold Commute SemiconjBy; rw [←transpose_mul, ←transpose_mul,(interlace ..).eq]
abbrev twistPins (d:ℕ)(p:EuPin):SpinPol d→ₐ[ℂ] SpinPol d:=Grass.adapter (turned p (wave p.matrix⁻¹.val)) (turned p (wave p.matrix.val.transpose))
lemma twist_mul (X:SpinPol d): twistPins _ p (twistPins _ q X)= twistPins _ (p*q) X:=by
    unfold twistPins; rw [Grass.adapt_together,reel,reel, wave_mul,wave_mul]; rw [show (p*q).matrix=p.matrix*q.matrix from rfl, Units.val_mul,transpose_mul,_root_.mul_inv_rev,Units.val_mul]
lemma twist_one (X:SpinPol d): twistPins d 1 X=X:=by unfold twistPins; rw [show (1:EuPin).matrix=1 from rfl]; simp [cool, wave_one]
lemma twist_color (u:su.El) (X:SpinPol d): twistPins _ p (adapter (colorTable u) (star (colorTable u)).transpose X) = adapter (colorTable u) (star (colorTable u)).transpose (twistPins _ p X):=by
   let X0:=touch (colour u); let S0:= wave p.matrix⁻¹.val; let T0:=wave p.matrix.val.transpose
   rw [alcohol (d:=d),groom]; change adapter _ _ (adapter (turned 1 X0) (turned 1 (star X0).transpose) X) = adapter _ _ (adapter (turned p S0) (turned p T0) X); rw [Grass.adapt_together, Grass.adapt_together,reel,reel,reel,reel,mul_one,one_mul]; rw [(interlace (colour u) p.matrix⁻¹.val).eq,(inter_opp (colour u) p.matrix.val).eq]

lemma axis_cap (x: Pol d)(h:x∈cap d): pinAct p x∈cap d:=by
   apply changeCap _ _ _ x h; rintro (i|i) (j|j) he
   · exact trails p _ _ _ he
   · rfl
   · rfl
   exact trails p _ _ _ he
private lemma hottest (p:EuPin)(u:su.El)(x:GPol) : (Labels.rotated p.coord) (Labels.changed (fun _=> Labels.Taylor.paint u) x)= Labels.changed (fun _=> Labels.Taylor.paint u) ((Labels.rotated p.coord) x):=by
   unfold Labels.rotated; apply Labels.eval_ext; intro J; simp_rw [Labels.eval_changed]; apply congr_arg (fun p=> Labels.read p x); funext i; exact Labels.Taylor.turn_paint .. -- orientation
lemma turnsF (u:su.El) (x:Pol d) : pinAct p (colorAct u x)=colorAct u (pinAct p x):=by
    induction x using TensorProduct.induction_on with
    | zero=> simp
    | tmul x y=> unfold pinAct colorAct; simp_rw [TensorProduct.map_tmul] ; exact congr_arg₂ (tmul ℂ) (hottest p u x) (twist_color p u y)
    | add x y hx hy=> simp only [map_add,hx,hy]
lemma orientP (x:Label d) : pinAct p x.val∈labels d:=by
    have hh:x.val∈ cap d ⊓ ⨅ u, LinearMap.ker (colorAct u - LinearMap.id):= x.property; change _∈ cap d ⊓ _; apply Submodule.mem_inf.mpr; refine ⟨axis_cap p _ hh.1,?_⟩
    simp only [Submodule.mem_iInf]; intro i; rw [LinearMap.mem_ker, LinearMap.sub_apply,sub_eq_zero,← turnsF]; have hI:colorAct i x.val=x.val:=by simp only [Submodule.mem_inf,Submodule.mem_iInf,LinearMap.mem_ker,LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply] at hh; exact hh.2 i
    rw [hI]; rfl
lemma burns (x:GPol): Labels.rotated 1 x=x:=by
   apply Labels.eval_ext; intro i; unfold Labels.rotated; rw [Labels.eval_changed]; apply congr_arg (fun i=>Labels.read i x); funext j; rw [inv_one]; exact Labels.Taylor.oneTurn _
lemma beam_pin (x:Pol d) : pinAct p (pinAct q x)=pinAct (p*q) x:=by
   induction x using TensorProduct.induction_on with
   | zero=> simp
   | tmul x y=> unfold pinAct; simp_rw [TensorProduct.map_tmul]; exact congr_arg₂ (fun x:GPol=>fun y:SpinPol d=> x ⊗ₜ[ℂ] y) (Labels.rotation_law p.coord q.coord x).symm (twist_mul p q y)
   | add x y hx hy=> simp [hx,hy]
@[simp] lemma pin_one (x:Pol d): pinAct 1 x=x:=by
   induction x using TensorProduct.induction_on with
   | zero=> simp
   | tmul x y=> unfold pinAct; rw [TensorProduct.map_tmul]; exact congr_arg₂ (fun x:GPol=> fun y:SpinPol d=>x ⊗ₜ[ℂ] y) (burns _) (twist_one _)
   | add x y hx hy=> simp [hx,hy]
-- share all polynomial basis.Pin.Table
noncomputable def pinCore (d:ℕ)(p:EuPin): Label d≃ₗ[ℂ]Label d where
  toFun x := ⟨pinAct p x.val,orientP p x⟩
  invFun x := ⟨pinAct p⁻¹ x.val,orientP p⁻¹ x⟩
  left_inv x:= Subtype.ext (Eq.trans (beam_pin p⁻¹ p _) (by simp))
  right_inv x:= Subtype.ext (Eq.trans (beam_pin p p⁻¹ _) (by simp))
  map_add' x y:= Subtype.ext (map_add (pinAct p) x.val y.val)
  map_smul' u x:= Subtype.ext (map_smul (pinAct p) u x.val)
end YM.Massive.UV
#print axioms YM.Massive.UV.pinCore
