import YM.Oriole.Gay
/-! single component prices.Sym all orientations. direct equalities. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)
open Poised.Display Poised.Stative Module Finset Revolve
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "W"=>CensusA d
variable (p q:Multi d)(D:CensusA d)(g:Bool)(M:Bundle)(s:Signed)
local notation "P"=> fun x:Fiber=> ((p,x),a)
local notation "Q"=> fun x:Fiber=> ((q,x),b)
noncomputable def fieldB : CensusA d:= ∑ i:Fiber,∑ j:Fiber,Matrix.single ((p,i),a) ((q,j),b) (M i j)
local notation "Tt"=> fieldB a b p q M
lemma fieldK (x y:T): Tt x y=if x.1.1=p∧x.2=a∧y.1.1=q∧y.2=b then M x.1.2 y.1.2 else 0:=by
    unfold fieldB; simp_rw [Matrix.sum_apply,Matrix.single_apply]; rcases x with ⟨⟨z,i⟩,e⟩; rcases y with ⟨⟨w,j⟩,f⟩; change _=if z=p∧e=a∧w=q∧f=b then _ else 0
    split_ifs with h
    · obtain ⟨rfl,rfl,rfl,rfl⟩:=h; rw [sum_eq_single i]; simp;
      · intro k _ ht; apply sum_eq_zero; intro l _; simp[ht]
      simp
    apply sum_eq_zero; intro k _; apply sum_eq_zero; intro l _; rw [if_neg]; rintro ⟨hk,hl⟩; apply h; cases hk; cases hl; simp
lemma coreB : prism a b p q Tt=M:=by ext i j; unfold prism; rw [Matrix.of_apply, fieldK]; simp
lemma C_light (z:ℂ) : fieldB a b p q (z • M)= z • fieldB a b p q M:=by
     ext i j; rw [Matrix.smul_apply, fieldK, fieldK]; split; rfl
     exact (smul_zero _).symm
lemma j_single(i j:T)(c:ℂ): jcoat (Matrix.single i j c)=(1:GPol)⊗ₜ[ℂ] (c • (bar i * psi j)):=by
     change (1:GPol)⊗ₜ[ℂ] (-form _)= _; congr 1; simp_rw [form,Matrix.single_apply]; -- `if`
     rw [sum_eq_single i]; · have hh: psi j*bar i= -(bar i*psi j):= atom_flip (Sum.inl j) (Sum.inr i); rw [sum_eq_single j]; simp [hh]; intro x _ h; simp [h,h.symm]; simp
     · intro k _ h; apply sum_eq_zero; intro l _; simp [h,h.symm]
     simp
variable (Z:Spike)
lemma j_stard : jcoat (fieldB a b p q (wave Z))= UV.bilinear a b Z p q:=by
     unfold fieldB bilinear; rw [map_sum,TensorProduct.tmul_sum]; simp_rw [map_sum, j_single]; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; rw [sum_comm,Fintype.sum_prod_type,TensorProduct.tmul_sum]; apply sum_congr rfl; intro j _; rw [TensorProduct.tmul_sum]; apply sum_congr rfl; intro k _; rw[sum_eq_single k]; simp [Stew.rich]; intro l _ h; simp [Stew.rich,h]; simp
lemma charm : CharmC a b (bilinear a b Z p q):=by
     intro f; unfold bilinear; rw[pig_weight,← tmul_smul]; congr 1
     change pigment _ f (∑ i:Pinor,∑ j: Pinor,∑ k:Hue,Z i j • (other _ _ _ _ * male _ _ _ _))=_; simp_rw [map_sum,map_smul,map_mul,pig_b,pig_p,_root_.smul_mul_assoc,_root_.mul_smul_comm,smul_sum,smul_comm (paidM a b f) (Z _ _ : ℂ),paidM,mul_smul]
-- label
lemma C_bound(h:spinWeight p+spinWeight q≤ d) : bilinear a b Z p q∈UV.cap d:=by
      refine ivory _ _ h ?_; refine Submodule.sum_mem _ (fun x _=> Submodule.sum_mem _ (fun y _=> Submodule.sum_mem _ (fun z _=> ?_))); apply Submodule.smul_mem; exact Rim.payroll letterWeight (q_other p a _ _) (q_male q b _ _)
private lemma singletPlan (u:su.El)(i j:Hue) : ∑ k, (star (colour u k i))* (colour u k j)=if i=j then 1 else 0:=by
    let V:=colour u; change _=if _ then _ else _; rw [← Matrix.one_apply (α:=ℂ)]; exact congr_arg (fun x:Mat=> x i j) (Papyrus.Boat.starcolour u)
private lemma element (i j:Pinor)(u:su.El)(Z:ℂ): dyeS d u (∑ z:Hue, Z • (other p a i z*male q b j z))=∑ z:Hue,Z • (other p a i z*male q b j z):=by
   rw [← smul_sum,map_smul]; apply congr_arg (fun x:SpinPol d=> Z • x); simp_rw [map_sum,map_mul,drizzle_rev,drizzle,Finset.sum_mul, Finset.mul_sum, _root_.smul_mul_assoc,_root_.mul_smul_comm,smul_smul]; rw [sum_comm]; apply sum_congr rfl; intro x _; rw [sum_comm]; simp_rw [←Finset.sum_smul, singletPlan]; simp [ite_smul]
lemma C_edge(h:spinWeight p+spinWeight q≤ d) : bilinear a b Z p q∈labels d:=by
     rw [label_law]; refine ⟨C_bound a b p q Z h,fun g=>?_⟩; unfold bilinear; rw [paint_weight]; congr 1; rw [map_sum]; apply sum_congr rfl; intro i _; rw [map_sum]; apply sum_congr rfl; intro j _; exact element a b p q _ _ g _ -- order inspect
noncomputable def satin(h:spinWeight p+spinWeight q ≤ d): Label d :=⟨_, C_edge a b p q Z h⟩
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.j_stard
#print axioms YM.Massive.Oriole.satin
