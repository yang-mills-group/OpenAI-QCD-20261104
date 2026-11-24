import YM.Massive.Target.Statement

/-!
# Entire coefficients of transported label matrices

Work with the *same* label space. Only assert existence of extension by complex
matrices (incidentally polynomial). This does not yet construct the RealSpin
action; ties it later along complexified boosts. `Multi` are derivative values,
not coefficients. No Lie group or classification of representations needed.
Cf. `YM.Next.MAXWELL.Scripts`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Spinor
open QCD QCD.Lat
open Set Function Filter Tensor Analysis Complex
open scoped TensorProduct Matrix.Norms.Frobenius Topology BigOperators ContDiff

-- both matrices included so no rational inverse necessary in continuing
abbrev Ink := Axis → Axis → ℂ
abbrev ArrayS := Ink × (Spike × Spike)
def printS (p : EuPin) : ArrayS := (fun i j => ↑(p.coord.val i j),p.matrix.val,p.matrix⁻¹.val)

-- scalar coefficients in the print
def Lettering (f : EuPin → ℂ) := ∃ g : ArrayS → ℂ, Differentiable ℂ g ∧ ∀ p, g (printS p)=f p
namespace Lettering
lemma const (x : ℂ) : Lettering (fun _ => x) := ⟨_,differentiable_const _,fun _ => rfl⟩
variable {u v : EuPin→ℂ}
lemma congr (h : Lettering u) (H : ∀ p, u p=v p) : Lettering v := funext H ▸ h
lemma plus (h : Lettering u) (H : Lettering v) : Lettering (fun p => u p+v p) := by
  obtain ⟨u',hu,H'⟩ := h; obtain ⟨v',hv,H⟩ := H
  exact ⟨_,hu.add hv,by intro; simp [H',H]⟩
lemma mul (h : Lettering u) (H : Lettering v) : Lettering (fun p => u p*v p) := by
  obtain ⟨u',hu,H'⟩ := h; obtain ⟨v',hv,H⟩ := H
  exact ⟨_,hu.mul hv,by intro; simp [H',H]⟩
lemma coord (i j : Axis) : Lettering (fun p => ↑(p.coord.val i j)) := ⟨fun s => s.1 i j,by fun_prop,fun _=>rfl⟩
lemma fin {ι : Type*} {g : ι → EuPin → ℂ} (s : Finset ι) (h : ∀ i∈s, Lettering (g i)) :
    Lettering (fun p => ∑ i∈s, g i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const 0)
  | insert a s he ih => exact ((h a (Finset.mem_insert_self a s)).plus (ih fun b hb=>h b (Finset.mem_insert_of_mem hb))).congr (by simp [he])
lemma prod {ι : Type*} {g : ι → EuPin → ℂ} (s : Finset ι) (h : ∀ i∈s, Lettering (g i)) :
    Lettering (fun p => ∏ i∈s, g i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const 1)
  | insert a s he ih => exact ((h a (Finset.mem_insert_self a s)).mul (ih fun b hb=>h b (Finset.mem_insert_of_mem hb))).congr (by simp [he])
end Lettering

-- without any topology on the ambient off-shell polynomials
private def Block (W : Type*) [AddCommGroup W] [Module ℂ W] :=
    Submodule.span ℂ {p : EuPin → W| ∃ f, Lettering f ∧ ∃ v : W, p=fun s=> f s • v}
namespace Block
private lemma pure {W : Type*} [AddCommGroup W] [Module ℂ W] {f : EuPin→ℂ} (h : Lettering f) (v : W) :
    (fun s=>f s • v)∈ Block W := Submodule.subset_span ⟨f,h,v,rfl⟩
private lemma const {W : Type*} [AddCommGroup W] [Module ℂ W] (v : W) : (fun _ : EuPin=>v) ∈ Block W := by simpa using pure (Lettering.const 1) v
private lemma times {W : Type*} [Ring W] [Algebra ℂ W] {p q : EuPin→W} (hp:p∈ Block W)(hq:q∈ Block W): (fun x=> p x*q x)∈ Block W:=by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f,hf,v,rfl⟩:=hx
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g,hg,w,rfl⟩:=hx; simp only [smul_mul_smul_comm]; exact pure (hf.mul hg) _
    | zero => simp only [Pi.zero_apply,mul_zero]; exact (Block W).zero_mem
    | add x y _ _ hA hB=> simp only [Pi.add_apply,mul_add]; exact (Block W).add_mem hA hB
    | smul t p _ h=> simp only [Pi.smul_apply,mul_smul_comm]; exact (Block W).smul_mem t h
  | zero => simp only [Pi.zero_apply,zero_mul]; exact (Block W).zero_mem
  | add x y _ _ hA hB=> simp only [Pi.add_apply,add_mul]; exact (Block W).add_mem hA hB
  | smul t p _ h=> simp only [Pi.smul_apply,smul_mul_assoc]; exact (Block W).smul_mem t h
private lemma powering {W : Type*} [Ring W] [Algebra ℂ W] {p : EuPin → W} (hp:p∈Block W) (n:ℕ): (fun x=> p x ^ n)∈ Block W:=by
  induction n with
  | zero => simpa using const (1:W)
  | succ n h=> simpa only [pow_succ] using times h hp
private lemma many {W ι: Type*} [CommRing W] [Algebra ℂ W] (s : Finset ι) (f:ι→ EuPin→W)
    (hf:∀ i∈s, f i∈ Block W): (fun p=> ∏ i∈s, f i p)∈ Block W:=by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (1:W)
  | insert a s he ih => simp only [Finset.prod_insert he]; exact times (hf a (Finset.mem_insert_self a s)) (ih fun b hb=>hf b (Finset.mem_insert_of_mem hb))
private lemma sum {W ι : Type*} [AddCommGroup W] [Module ℂ W] (s : Finset ι) (f:ι→ EuPin→W)
    (hf:∀ i∈s, f i∈ Block W): (fun p=> ∑ i∈s, f i p)∈ Block W:=by
  have H := (Block W).sum_mem (t:=s) hf
  simpa only [←Finset.sum_apply] using H
private lemma torch {W V: Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ W] [Module ℂ V] {p : EuPin→W}{q : EuPin→V}(hp:p∈Block W)(hq:q∈Block V): (fun s=>p s ⊗ₜ[ℂ] q s)∈ Block _:= by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f,hf,v,rfl⟩:=hx
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g,hg,w,rfl⟩:=hx; simp only [←TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]; exact pure (hg.mul hf) (TensorProduct.tmul ℂ v w)
    | zero => simp only [Pi.zero_apply,TensorProduct.tmul_zero]; exact (Block _).zero_mem
    | add x y _ _ hA hB=> simp only [Pi.add_apply,TensorProduct.tmul_add]; exact (Block _).add_mem hA hB
    | smul t p _ h=> simp only [Pi.smul_apply,TensorProduct.tmul_smul]; exact (Block _).smul_mem t h
  | zero => simp only [Pi.zero_apply,TensorProduct.zero_tmul]; exact (Block _).zero_mem
  | add x y _ _ hA hB=> simp only [Pi.add_apply,TensorProduct.add_tmul]; exact (Block _).add_mem hA hB
  | smul t p _ h=> simp only [Pi.smul_apply,←TensorProduct.smul_tmul']; exact (Block _).smul_mem t h
private lemma budget {W: Type*} [AddCommGroup W] [Module ℂ W] {p : EuPin → W}(hp:p∈Block W)(X : Module.Dual ℂ W) : Lettering (fun q=> X (p q)) := by
  induction hp using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f,hf,v,rfl⟩:=hy; simp only [map_smul,smul_eq_mul]; exact hf.mul (Lettering.const _)
  | zero => simp only [Pi.zero_apply,map_zero]; exact Lettering.const _
  | add v w _ _ hv hw => simp only [Pi.add_apply,map_add]; exact hv.plus hw
  | smul t p _ hp => simp only [Pi.smul_apply,map_smul,smul_eq_mul]; exact (Lettering.const _).mul hp
private lemma mul_X {σ : Type*} {f : EuPin→ℂ}(h:Lettering f)(a:σ):
    (fun p=> MvPolynomial.C (f p) * MvPolynomial.X a)∈ Block (MvPolynomial σ ℂ) := by
  have H : ∀ c : ℂ, MvPolynomial.C c * MvPolynomial.X a=c • MvPolynomial.X a := fun c=> MvPolynomial.C_mul'
  simp_rw [H]; exact pure h _
end Block

namespace Vertex
open UV
variable {n d : ℕ}
private lemma value (A : Labels.Taylor su n) (a : Axis) (x : E4) (k : su.ColorIndex) : Lettering (fun p=> ((Labels.Taylor.turn p.coord⁻¹ A).value a x k:ℂ)) := by
   let g (p:EuPin) := Ortho.move p.coord x
   have hG (l:Axis) : Lettering fun p=> (g p l:ℂ) := by
      simp only [g,Ortho.move,M4.at_coord, Complex.ofReal_sum,Complex.ofReal_mul]; apply Lettering.fin; intro i _; exact (Lettering.coord _ _).mul (Lettering.const _)
   have hX(i : Axis) : Lettering fun p=> (A.value i (g p) k:ℂ) := by
      let f (p:EuPin) (w: Fin (n+1)→Axis):ℝ := ∏ j : Fin (n+1), g p (w j)
      have h (p:EuPin) : A.value i (g p)= ∑ w: Fin (n+1)→Axis, f p w • A.val i (basis ∘ w) := by
        let z (k:Axis) := g p k • basis k
        unfold Labels.Taylor.value Tensor.diagonal
        conv_lhs=> arg 2; ext j; rw [show g p=∑ k,z k from by ext k; simp [z]]
        rw [ContinuousMultilinearMap.map_sum]; apply Finset.sum_congr ?_
        · intro k _; exact (A.val i).map_smul_univ _ _
        ext w; simp
      simp_rw [h,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul,f,Complex.ofReal_prod]
      apply Lettering.fin; intro w _; exact (Lettering.prod _ (fun j _=>hG (w j))).mul (Lettering.const _)
   simp_rw [Labels.Taylor.turn_value, inv_inv,WithLp.ofLp_sum,Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]
   apply Lettering.fin; intro i _
   have h (p:Ortho): p⁻¹.val a i=p.val i a:=rfl
   simp only [h]; exact (Lettering.coord _ _).mul (hX i)
private def placeV (a : Axis) (x : E4) (k : su.ColorIndex) : Module.Dual ℝ (Labels.Taylor su n) where
   toFun A := A.value a x k
   map_add' _ _ := rfl
   map_smul' _ _ := rfl
private def plots (q : Axis× E4 × su.ColorIndex) : Module.Dual ℝ (Labels.Taylor su n) := placeV q.1 q.2.1 q.2.2
private lemma spans (n : ℕ) : Submodule.span ℝ (Set.range (@plots n))= ⊤ := by
   let V:= Submodule.span ℝ (Set.range (@plots n))
   change V=⊤
   have he : V.dualCoannihilator=⊥:=by
      apply le_antisymm _ bot_le; intro A hA; apply (Submodule.mem_bot ..).mpr
      apply Labels.Taylor.value_ext; funext a x; ext k
      change placeV a x k A=0
      exact (Submodule.mem_dualCoannihilator _).1 hA _ (Submodule.subset_span ⟨(a,x,k),rfl⟩)
   apply Submodule.eq_top_of_finrank_eq
   have hm := Subspace.finrank_add_finrank_dualCoannihilator_eq V
   rw [he,finrank_bot,add_zero] at hm
   rw [hm,Subspace.dual_finrank_eq]
private lemma valueT (A : Labels.Taylor su n) (X : Module.Dual ℝ (Labels.Taylor su n)) : Lettering (fun p=> (X (Labels.Taylor.turn p.coord⁻¹ A):ℂ)) := by
   refine Submodule.span_induction (p := fun X _ => Lettering (fun p=> (X (Labels.Taylor.turn p.coord⁻¹ A):ℂ))) ?_ ?_ ?_ ?_ (show X∈_ from spans n |>.symm ▸ Submodule.mem_top)
   · rintro _ ⟨⟨a,x,k⟩,rfl⟩; exact value A a x k
   · simp only [LinearMap.zero_apply,ofReal_zero]; exact Lettering.const _
   · intro i j _ _ H K; simp only [LinearMap.add_apply,ofReal_add]; exact H.plus K
   intro c i h H; simp only [LinearMap.smul_apply, smul_eq_mul, ofReal_mul]; exact (Lettering.const _).mul H

private lemma gauge (x : GPol) : (fun p:EuPin=> Labels.rotated p.coord x)∈ Block GPol:=by
  induction x using MvPolynomial.induction_on with
  | C a => simp only [Labels.rotated,Labels.changed,MvPolynomial.aeval_C]; exact Block.const _
  | add x y hx hy => simp only [map_add]; exact (Block _).add_mem hx hy
  | mul_X x k hx =>
    simp only [map_mul]; apply Block.times hx
    simp only [Labels.rotated,Labels.changed,MvPolynomial.aeval_X]; apply Block.sum; intro j _
    exact Block.mul_X (valueT (Labels.axes su k.1 j) ((Labels.axes su k.1).coord k.2)) _

private lemma move (i j : Multi d) : Lettering (fun p => multiMove p i j) := by
   unfold multiMove
   let f (a : Axis) (p : EuPin) : MvPolynomial Axis ℂ := ∑ b : Axis,
     MvPolynomial.C (p.coord.val b a : ℂ) * MvPolynomial.X b
   have he (a:Axis): f a∈ Block (MvPolynomial Axis ℂ):=by unfold f; apply Block.sum; intro i _; exact Block.mul_X (Lettering.coord _ _) _
   exact Block.budget (Block.many Finset.univ (fun a p=> f a p ^ power i a) (fun b _=> Block.powering (he _) _)) (MvPolynomial.lcoeff ℂ (Finsupp.equivFunOnFinite.symm (power j)))

private lemma letterM (i j:QCD.Lat.Pinor) : Lettering (fun p=> p.matrix.val i j) ∧ Lettering (fun p => p.matrix⁻¹.val i j) := by
  -- don't use Differentiable on a Pi unfolded with wrong norm
  let f : Spike →ₗ[ℂ] ℂ := { toFun x:=x i j, map_add' _ _:=rfl, map_smul' _ _:=rfl }
  constructor
  · exact ⟨f.toContinuousLinearMap ∘ Prod.fst ∘ Prod.snd, f.toContinuousLinearMap.differentiable.comp (differentiable_fst.comp differentiable_snd),fun _=>rfl⟩
  · exact ⟨f.toContinuousLinearMap ∘ Prod.snd ∘ Prod.snd, f.toContinuousLinearMap.differentiable.comp (differentiable_snd.comp differentiable_snd),fun _=>rfl⟩

private lemma letters (p : EuPin → Spike) (h:∀ i j,Lettering (fun q=> p q i j)) (i j:SpinMode d): Lettering (fun q=> UV.turned q (wave (p q)) i j) := by
   classical
   unfold UV.turned; simp only [Matrix.of_apply]; split_ifs
   · apply Lettering.mul (move _ _)
     simp only [wave, Matrix.kroneckerMap_apply]; exact (h _ _).mul (Lettering.const _)
   exact Lettering.const _

private abbrev twist (p:EuPin) (d:ℕ):= Grass.adapter (UV.turned (d:=d) p (wave p.matrix⁻¹.val)) (UV.turned (d:=d) p (wave p.matrix.val.transpose))

private lemma spice (x : SpinPol d) : (fun p:EuPin=> twist p d x) ∈ Block _ := by
   classical
   induction x using ExteriorAlgebra.induction with
   | algebraMap s=> simp only [AlgHom.commutes]; exact Block.const _
   | ι v =>
     rw [Grass.line_atoms]
     simp only [map_sum,map_smul]; apply Block.sum; intro i _; apply (Block _).smul_mem
     rcases i with i|i
     · simp only [twist,Grass.adapter, Grass.change_atom]; apply Block.sum; intro j _; apply Block.pure
       rcases j with j|j; exact letters _ (fun i j=>(letterM i j).2) i j; exact Lettering.const _
     · simp only [twist,Grass.adapter, Grass.change_atom]; apply Block.sum; intro j _; apply Block.pure
       rcases j with j|j; exact Lettering.const _; exact letters _ (fun i j=>(letterM j i).1) i j
   | add x y hx hy => simp only [map_add]; exact (Block _).add_mem hx hy
   | mul x y hx hy => simp only [map_mul]; exact Block.times hx hy

lemma figures (x : Pol d) (K : Module.Dual ℂ (Pol d)) : Lettering fun p=> K (pinAct p x):=by
   apply Block.budget
   induction x using TensorProduct.induction_on with
   | zero=> simp only [map_zero]; exact Block.const _
   | tmul x y=>
     simp only [pinAct,TensorProduct.map_tmul,AlgHom.toLinearMap_apply]
     exact Block.torch (gauge x) (spice y)
   | add x y hx hy=> simp only [map_add]; exact (Block _).add_mem hx hy
end Vertex
end YM.Massive.Bridge.Spinor
