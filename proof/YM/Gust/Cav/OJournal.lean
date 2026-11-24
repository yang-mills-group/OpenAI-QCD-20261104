import YM.Next.ROTATIONS.Journal
import YM.Gust.Cav.OPairs
/- Variant of YM.Next.ROTATIONS.Journal, for Spiral register. -/
noncomputable section
namespace YM.Spiral.Outer
open YM.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L}
structure Portrait (J : Stress S) (D : ℕ) (R : Series) : Prop where
  agrees a b c d : ∀ f : Panels, ∀ i, flat D (f i) → (R a b c d) f=∫ x,linePair J a b c d x * tensor f x
  LR a b c d : R a b c d=R b a c d
  UD a b c d : R a b c d=R c d a b
  Hs (s : Signed) (a b c d) (f : Panels) :
    (colorSign s a*colorSign s b*(colorSign s c*colorSign s d))*
        (R (s.perm a) (s.perm b) (s.perm c) (s.perm d)) (moves s f)=(R a b c d) f
lemma inverted_pair (H : S.Hierarchy) (J : Stress S) (h : RawTensor H.spin J) (a b c d x) (hx : x ≠ 0) :
    linePair J a b c d (-x)=linePair J a b c d x := by
  have he := moved_pair H J h a b c d invert4 x hx
  rw [show Ortho.move invert4.ortho x= -x by rw [Signed.ortho_move]; ext i; simp [invert4,Signed.act]] at he
  simpa only [invert4,colorSign,signValue,↓reduceIte,neg_mul_neg,mul_one,one_mul,Equiv.refl_apply] using he
lemma portrays (H : S.Hierarchy) (J : Stress S) (h : RawTensor H.spin J) (hJ : ∀ i j,J i j = J j i) (D : ℕ) (hp : ∀ i j k l, ScaleCap D (linePair J i j k l)) :
    ∃ R : Series, Portrait J D R := by
  let R := fun i j k l => article (linePair J i j k l) D (hp ..) (pair_meas H ..)
  have hh : ∀ᵐ p : E4, p≠0 := by simp only [ae_iff]; simp
  refine ⟨R,fun i j k l f a ha => article_test f a ha,?_,?_,?_⟩
  · intro i j k l; unfold R linePair tag; simp_rw [hJ i j]
  · intro i j k l; ext1 f
    change (∫ y,battle _ D f y)= _
    refine integral_congr_ae (hh.mono fun x hx => ?_)
    unfold battle
    rw [show linePair J i j k l x = linePair J k l i j (-x) from pair_flip H _ _ hx,inverted_pair H J h _ _ _ _ _ hx]
  · intro s i j k l f
    let Z := Ortho.motion s.ortho
    change _*(∫ y,battle _ _ _ y)= _
    rw [← Z.measurePreserving.integral_comp Z.toHomeomorph.measurableEmbedding,← integral_const_mul]
    refine integral_congr_ae (hh.mono fun x hx => ?_)
    dsimp only [battle,Z,Ortho.motion_at]
    rw [tensor_moves,moves_projections,tensor_moves,← mul_assoc,moved_pair H J h i j k l s x hx]
private lemma prime_glare (f : Form) : prime (glare f) = -(glare (prime f)) := by
  ext t; change deriv (fun x : ℝ => f (-x)) t= -deriv f (-t)
  exact deriv_comp_neg .. 
private lemma shifts_move (s : Signed) (a : Axis) (f : Panels) :
    moves s (moved a f) = update (moves s f) (s.perm a) (colorSign s a • prime (moves s f (s.perm a))) := by
  ext1 i
  obtain ⟨i,rfl⟩ := s.perm.surjective i
  rw [moves_perm]; unfold moved
  by_cases h : i=a
  · subst i; rw [update_self, update_self,moves_perm,colorSign]; cases h : s.flip a <;> simp [reflectPanel,signValue,prime_glare]
  rw [update_of_ne h ..,update_of_ne (s.perm.injective.ne h),moves_perm]
lemma delta_turn {R J D} (H : Portrait (S:=S) J D R) (b c d : Axis) (s : Signed) (f) :
    (colorSign s b * (colorSign s c*colorSign s d)) * delta R (s.perm b) (s.perm c) (s.perm d) (moves s f)=
      delta R b c d f := by
  rw [delta_at,delta_at,← Equiv.sum_comp s.perm,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [← H.Hs s _ _ _ _ (moved a f), shifts_move,
    MultilinearMap.map_update_smul]
  unfold moved; simp only [smul_eq_mul]
  -- cancel colorSign a
  cases ha : s.flip a <;> simp only [colorSign,ha,signValue] <;> split_ifs <;> simp
lemma writer_move {R J D} (H : Portrait (S:=S) J D R) (a b c d : Axis) (s : Signed) :
    (colorSign s a* colorSign s b*(colorSign s c*colorSign s d))*
        writer R (s.perm a) (s.perm b) (s.perm c) (s.perm d)=writer R a b c d := by
  unfold writer; rw [← delta_turn H b c d s (once a),
    show moves s (once a) = update (fun _ => gen 0) (s.perm a) (colorSign s a • gen 1) from ?_, MultilinearMap.map_update_smul]
  · unfold once; simp only [smul_eq_mul]; ring
  funext i
  obtain ⟨i,rfl⟩ := s.perm.surjective i
  rw [moves_perm]; unfold once
  by_cases h : i=a
  · subst i; rw [update_self,update_self]; cases h : s.flip a <;> simp [reflectPanel,colorSign,signValue,h,gen_flip]
  rw [update_of_ne h,update_of_ne (s.perm.injective.ne h)]
  cases he : s.flip i <;> simp [reflectPanel,gen_flip]
private def Bin (a b c d : Axis) := (a=b ∧ c=d) ∨ (a=c ∧ b=d) ∨ (a=d ∧ b=c)
private lemma parity (a b c d : Axis) (h : ¬ Bin a b c d) : ∃ i,twin a b c d (Signed.mirror i)= -1 := by
  by_cases hb : a=b
  · subst b; refine ⟨c,?_⟩
    have he : c≠d := fun e => h (Or.inl ⟨rfl,e⟩)
    unfold twin colorSign; rw [sign_sq]; simp [Signed.mirror,signValue,he]
  by_cases he : a=c
  · subst c
    have hx : b≠d := fun e => h (Or.inr (Or.inl ⟨rfl,e⟩))
    exact ⟨b,by simp [twin,colorSign,signValue,Signed.mirror,Ne.symm hb,hx]⟩
  by_cases hp : a=d
  · subst d; have hu : b≠c := fun e => h (Or.inr (Or.inr ⟨rfl,e⟩))
    exact ⟨c, by simp [twin,colorSign,signValue,Signed.mirror,Ne.symm he,Ne.symm hu]⟩
  exact ⟨a,by simp [twin,colorSign,signValue,Signed.mirror,hb,he,hp]⟩
private lemma writer_off {R J D} (H : Portrait (S:=S) J D R) (a b c d : Axis) (h : ¬ Bin a b c d) : writer R a b c d=0 := by
  obtain ⟨i,h⟩ := parity _ _ _ _ h
  have ht := writer_move H a b c d (Signed.mirror i); dsimp only [twin] at h; rw [h] at ht
  change (-1:ℂ)*writer R a b c d= _ at ht
  rw [neg_one_mul] at ht; exact neg_eq_self.mp ht
lemma Partner {R J D} (H : Portrait (S:=S) J D R) (a b c d : Axis) : R a b c d = R a b d c := by rw [H.UD a b c d,H.LR c d,H.UD]
lemma symmetric_writer {R J D} (H : Portrait (S:=S) J D R) (a b c d : Axis) :
    writer R a b c d=writer R b a c d ∧ writer R a b c d=writer R c d a b := by
  by_cases h : Bin a b c d
  · have ht (a b i j : Axis) : writer R a b i j=writer R a b j i := by unfold writer; simp_rw [delta_at, Partner H _ b i j]
    have hv (a b i j : Axis) (s : Equiv.Perm Axis) : writer R a b i j= writer R (s a) (s b) (s i) (s j) := by
      simpa [colorSign,signValue] using (writer_move H a b i j ⟨s,fun _ => false⟩).symm
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨rfl,by simpa using hv a a c c (Equiv.swap a c)⟩
    · rw [← ht b a b a]; exact ⟨by simpa using hv a b a b (Equiv.swap a b), rfl⟩
    · have he := hv a b b a (Equiv.swap a b)
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at he
      rw [he]; exact ⟨ht .., rfl⟩
  · rw [writer_off H _ _ _ _ h, writer_off H b a c d ?_, writer_off H c d a b ?_]; all_goals unfold Bin at *; all_goals grind
lemma joined {R J D} (h : Portrait (S:=S) J D R) (he : 0<D) : Portrait J D (joint R) := by
  refine ⟨?_,fun a b c d => ?_,fun a b c d => ?_,?_⟩
  · intro a b c d f i hi
    rw [joint_at,h.agrees a b c d f i hi,onZero_at,tensor_at,Finset.prod_eq_zero (Finset.mem_univ i),mul_zero,sub_zero]
    simpa using hi 0 he
  · unfold joint; rw [(symmetric_writer h ..).1,h.LR]
  · unfold joint; rw [(symmetric_writer h ..).2,h.UD]
  · intro s a b c d f; rw [joint_at,joint_at,mul_sub,h.Hs,onZero_move,← mul_assoc,writer_move h a b c d s]
lemma inversion_nil {D J R} (h : Portrait (S:=S) J D R) (b c d : Axis) (p : Axis→ℕ) (H : Even (∑ i,p i)) :
    delta R b c d (formal p)=0 := by
  have he := delta_turn h b c d invert4 (formal p)
  have hh : moves invert4 (formal p)=fun i => (-1:ℂ)^(p i) • formal p i := by
    ext1 i; exact gen_flip _
  rw [hh] at he
  change (-1:ℂ) * ((-1:ℂ)*(-1:ℂ)) * (delta R b c d _) = _ at he
  rw [MultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum] at he
  apply neg_eq_self.mp; simpa only [H.neg_one_pow,neg_mul_neg,one_mul,neg_mul,one_smul,neg_neg] using he
lemma joint_null {R J D} (H : Portrait (S:=S) J D R) (h : 0<D) (b c d : Axis) (p : Axis → ℕ) (he : (∑ i,p i) < 3) :
    delta (joint R) b c d (formal p)=0 := by
  let s := ∑ i,p i
  change s<3 at he
  rcases show s=0 ∨ s=2 ∨ s=1 by omega with hs|hs|hs
  · apply inversion_nil (joined H h); rw [show (∑ i,p i)=_ from hs]; decide
  · apply inversion_nil (joined H h); rw [show (∑ i,p i)=_ from hs]; decide
  · obtain ⟨i,hi⟩ : ∃ i, p i ≠ 0 := by by_contra! hx; simp [s,hx] at hs
    have ht : p i=1 := by have hp' := show p i ≤ s from Finset.single_le_sum (f:=p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i); omega
    have hu j (hh : j≠i) : p j=0 := by
      have hz : p i+p j ≤ s := by
        refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg (s:={i,j}) (t:=Finset.univ) (f:=p) (by simp) (fun _ _ _ => Nat.zero_le _))
        simp [Ne.symm hh]
      omega
    rw [show formal p=once i by
      funext j; unfold formal once; by_cases hh : j=i
      · subst j; rw [ht,update_self]
      · rw [hu _ hh,update_of_ne hh]]
    exact joint_home ..
end YM.Spiral.Outer

