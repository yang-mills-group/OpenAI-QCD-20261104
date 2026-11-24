import YM.Massive.Hawser.Temple
/-! # Odd baryon orbit (with orientation determinant before computing rank projection). -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.UV
open Lattice Wilson RG Source Function QCD Lat Massive Lining Papyrus Filter Work.G05 Finset Matrix Grass TensorProduct
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker TensorProduct
variable {d:ℕ}(i j k:Pinor)
local notation "P" => Equiv.Perm Hue
namespace Pearl
abbrev Triple := Hue×Hue×Hue
local notation "V" => SpinPol 9
def ψ (v:Triple): Hue→Hue:= ![v.1,v.2.1,v.2.2]
def D (v:Triple)(T:Mat):Mat:= Matrix.of fun i j=> T i (ψ v j)
private lemma cost (v: Triple) (T:Mat): D v T=T* D v 1:=by
    ext i j; unfold D; rw [Matrix.mul_apply]; simp [Matrix.one_apply, mul_ite]; -- order
abbrev isk (x : Hue) := male (0:Multi 9) (0:Flavor 6) i x
abbrev esk (x : Hue) := male (0:Multi 9) (1:Flavor 6) j x -- implicit j? variable inclusion
abbrev ots (x : Hue) := male (0:Multi 9) (2:Flavor 6) k x
def rowW (v:Triple) : V:= isk i v.1 * esk j v.2.1 * ots k v.2.2
def α (σ:P):Triple:= (σ 0,σ 1,σ 2)
def ε (σ:P) : ℂ:= ((Equiv.Perm.sign σ : ℤ): ℂ)
def φ (T:Mat)(σ:P) : V:= ((∑ x, T (σ 0) x • isk i x)*(∑ x,T (σ 1) x • esk j x))*(∑ x,T (σ 2) x • ots k x)
lemma φ_one (σ:P) : φ i j k 1 σ=rowW i j k (α σ):=by unfold φ; simp only [one_apply, ite_smul, zero_smul, one_smul,sum_ite_eq, mem_univ, if_true]; rfl
private lemma among {X:Type*}[AddCommMonoid X](F:Hue→Hue→Hue→X): (∑ x,∑ y, ∑ z,F x y z)= ∑ z,∑ y,∑ x,F x y z:=by
   rw [sum_comm, sum_comm (f:=fun z y=> ∑ x,F x y z)]; apply sum_congr rfl; intro i _; rw [sum_comm]
lemma φs (T:Mat)(σ:P) : φ i j k T σ=∑ v:Triple, (∏ p, D v T (σ p) p) • rowW i j k v:=by
    unfold φ; simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]; simp_rw [_root_.smul_mul_assoc,_root_.mul_smul_comm]; rw [among]; refine sum_congr rfl fun u _=> sum_congr rfl fun v _ => sum_congr rfl fun x _=> ?_; rw [Fin.prod_univ_succ]; simp [Fin.prod_univ_succ,mul_smul,D,Pearl.ψ,rowW]; rw [smul_comm (T (σ 2) _) (T (σ 1) _)]
def lighthouse : V:= ∑ s:P, ε s • rowW i j k (α s)
def cruise (T : Mat) := ∑ s:P, ε s • φ i j k T s
lemma till (T:Mat) : cruise i j k T=T.det • lighthouse i j k:=by
    unfold cruise lighthouse; have ht (T:Mat): (∑ s:P, ε s • φ i j k T s)=∑ v:Triple,(D v T).det • rowW i j k v:=by
          simp_rw [φs, smul_sum, smul_smul]; rw [sum_comm]; apply sum_congr rfl; intro v _; rw [← sum_smul, det_apply']; rfl
    simp_rw [← φ_one]; rw [ht,ht]; simp_rw [show ∀ v, (D v T).det=T.det*(D v 1).det from fun v=>by rw [cost, Matrix.det_mul], mul_smul, smul_sum]
lemma sign_penguin {E:Type*}[AddCommGroup E][Module ℂ E](x:E)(σ:P): Equiv.Perm.sign σ • x= ε σ • x:= by rw [Units.smul_def, ε, Int.cast_smul_eq_zsmul ℂ]
lemma τ : UV.baryon i j k=(1:GPol) ⊗ₜ[ℂ] lighthouse i j k:= by unfold baryon lighthouse; simp_rw [sign_penguin]; rfl
variable (u:su.El)
lemma paint_φ (T:Mat)(σ:P) (ht:T=colour u) : dyeS 9 u (rowW i j k (α σ))=φ i j k T σ:=by unfold rowW; rw [map_mul,map_mul]; rw [isk,esk,ots,drizzle,drizzle,drizzle,ht]; rfl -- rfl
lemma light_color : dyeS 9 u (lighthouse i j k)=lighthouse i j k:=by
   nth_rw 1 [lighthouse]; simp_rw [map_sum,map_smul, fun s=> paint_φ i j k u (colour u) s rfl]; change cruise i j k _=_; rw [till,show (colour u).det=1 from det_su u,one_smul]
private lemma buoy (v:Triple): rowW i j k v∈weightS 9:=by
   unfold rowW; let e:= spinWeight (0:Multi 9); have hh : isk i v.1 * esk j v.2.1 * ots k v.2.2∈ weightS (e+e+e):= Rim.payroll letterWeight (Rim.payroll letterWeight (q_male (0:Multi 9) 0 i v.1) (q_male (0:Multi 9) 1 j v.2.1)) (q_male (0:Multi 9) 2 k v.2.2); unfold e at hh; rw [cost_root] at hh; exact hh
lemma pearl : lighthouse i j k∈weightS 9:= Submodule.sum_mem _ fun s _=> Submodule.smul_mem _ _ (buoy i j k (α s))
lemma odd_lamp : grade (lighthouse i j k) = -lighthouse i j k:=by simp only [lighthouse,map_sum,map_smul,rowW,isk,esk,ots,male,Grass.psi,map_mul,grade_atom,neg_mul,neg_neg,mul_neg,smul_neg,sum_neg_distrib] -- namespace ψ conflict ok
abbrev lit (u:FlavorTorus): ℂ:= (u 0).val*(u 1).val*(u 2).val
lemma weighted (u:FlavorTorus): pigment _ u (lighthouse i j k)= (lit u) • lighthouse i j k:=by
    unfold lighthouse; simp_rw [map_sum,map_smul,rowW,map_mul,isk,esk,ots,pig_p,_root_.smul_mul_assoc,_root_.mul_smul_comm,smul_sum,smul_comm (lit u) (ε _),lit,mul_smul,_root_.smul_mul_assoc, smul_comm (u 2).val (u 1).val]; -- rfl
lemma rock_label (i j k:Pinor) : UV.baryon i j k∈labels 9:=(label_law _).mpr (by
    rw [τ]; exact ⟨ivory _ 9 le_rfl (pearl i j k),fun u=> by rw [paint_weight,light_color]⟩)
noncomputable def rock (i j k:Pinor): Label 9:=⟨_,rock_label i j k⟩
lemma rockW (W: RawSym) : W.parity 9 (rock i j k)= -(rock i j k):= by apply Subtype.ext; rw [W.parityActs]; change parityAct (UV.baryon _ _ _)= - UV.baryon _ _ _; rw [τ,parity_weight,odd_lamp,TensorProduct.tmul_neg]
lemma rockF (W:RawSym)(p:FlavorTorus) : W.flavor 9 p (rock i j k)= lit p • rock i j k:= by apply Subtype.ext; rw [W.flavorActs]; change flavorAct p (baryon i j k)= lit p • baryon i j k; rw [τ,pig_weight,weighted,tmul_smul]
end Pearl
end YM.Massive.UV
#print axioms YM.Massive.UV.Pearl.rockW
