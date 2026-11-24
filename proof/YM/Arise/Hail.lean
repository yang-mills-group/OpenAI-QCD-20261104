import YM.Arise.Halo
/-! # Signed turnings of the actual radial moment. Center correction handled on the complete plate before Reynolds. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise
open Function Lattice Finset Wilson Filter MeasureTheory Tensor
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Pointwise
-- Orientation of G apertures.
variable {r n m i j l k d:ℕ}
variable {F :Type*}[NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F]
variable (s t: Signed)(x:Cover)(a b:Axis)(p:PlaqAxes)
def hue (s: Signed)(a:Axis): ℝ:= if s.flip a then -1 else 1
def vane (l: List Axis):= List.prod (l.map (hue s))
lemma hue_id: hue (1:Signed) a=1:=by simp [hue]
lemma hue_mul : hue (s*t) a=hue s (t.perm a)*hue t a:=by by_cases hp:s.flip (t.perm a)=true <;> by_cases hh:t.flip a=true <;> simp [hue,hp,hh]
lemma hue_sq: hue s a*hue s a=1:=by unfold hue; split<;> ring
def sways (l:List Axis):= l.map s.perm
lemma vane_id (l:List Axis):vane (1:Signed) l=1:=by induction l with|nil=>rfl|cons a v ih=>change hue _ _*vane _ v=_; rw [hue_id,ih,mul_one]
lemma vane_mul (l:List Axis): vane (s*t) l=vane s (sways t l)*vane t l:=by induction l with|nil=> simp[vane,sways]|cons a l ih=>change hue _ _* vane _ l=(hue _ _*vane _ _)*(hue _ _*vane _ _); rw [hue_mul,ih]; unfold sways; ring
lemma vane_sq (l:List Axis): vane s l*vane s l=1:=by induction l with|nil=>simp [vane]|cons a v ih=> rw [show vane s (a::v)=hue s a*vane s v from rfl,mul_mul_mul_comm,hue_sq,ih,mul_one]
lemma sways_len (l:List Axis): (sways s l).length=l.length:=by simp [sways]
lemma sways_id (l:List Axis):sways 1 l=l:=by simp [sways] -- maybe done
lemma sways_mul(l:List Axis): sways (s*t) l=sways s (sways t l):=by simp only [sways,List.map_map]; rfl -- maybe Coe Eq.def
def tw (i j: Axis)(h:i ≠ j):PlaqAxes := if hi:i < j then ⟨(i,j),hi⟩ else ⟨(j,i),lt_of_le_of_ne (le_of_not_gt hi) h.symm⟩
def took (s:Signed)(p:PlaqAxes):= tw (s.perm p.val.1) (s.perm p.val.2) (s.perm.injective.ne p.property.ne)
def glyphO := (if s.perm p.val.1<s.perm p.val.2 then 1 else -1)*hue s p.val.1*hue s p.val.2
def dent (i:Axis): Cover:= if s.flip i then -(step (s.perm i)) else 0
def bend := dent s p.val.1+dent s p.val.2
def porch (q:Option PlaqAxes):Cover:= match q with | some p=> bend s p|none=>0
lemma took_start : took 1 p=p:=by
    unfold took tw; split; next ht=> rfl
    next ht=> exact (ht p.property).elim
lemma took_mul: took (s*t) p=took s (took t p):=by
    let i:= s.perm (t.perm p.val.1); let j:=s.perm (t.perm p.val.2); have hp:i≠j:= (s.perm.injective.ne (t.perm.injective.ne p.property.ne)); apply Subtype.ext; unfold took; by_cases ht:t.perm p.val.1<t.perm p.val.2 <;> by_cases h:i < j
    · simp only [tw,Signed.mul_perm_apply, (show s.perm (t.perm p.val.1)<s.perm (t.perm p.val.2) from h),ht,↓reduceDIte]
    · have he:j < i :=lt_of_le_of_ne (le_of_not_gt h) hp.symm; simp only [tw,ht,Signed.mul_perm_apply, ↓reduceDIte]
    · simp only [tw,ht,Signed.mul_perm_apply, (show ¬ s.perm (t.perm p.val.2)<s.perm (t.perm p.val.1) from not_lt_of_gt h), (show s.perm (t.perm p.val.1)<s.perm (t.perm p.val.2) from h),↓reduceDIte]
    · have he:j < i :=lt_of_le_of_ne (le_of_not_gt h) hp.symm; have hh:¬ s.perm (t.perm p.val.1)<s.perm (t.perm p.val.2):=not_lt_of_gt he; simp only [tw,ht,Signed.mul_perm_apply,hh,(show s.perm (t.perm p.val.2)<s.perm (t.perm p.val.1) from he),↓reduceDIte]
lemma glyph_one : glyphO 1 p=1:=by unfold glyphO; rw [ Signed.one_perm,Equiv.refl_apply,Equiv.refl_apply, if_pos p.property,hue_id,hue_id]; ring
lemma glyph_pin : glyphO s p*glyphO s p=1:=by unfold glyphO; rw [mul_mul_mul_comm (_*_),mul_mul_mul_comm (ite _ _ _),hue_sq,hue_sq]; split<;> ring
lemma glyph_mul: glyphO (s*t) p=glyphO s (took t p)*glyphO t p:=by
    let i:= s.perm (t.perm p.val.1); let j:=s.perm (t.perm p.val.2); have hp:i≠j:= (s.perm.injective.ne (t.perm.injective.ne p.property.ne)); have he:s.perm (t.perm p.val.2)<s.perm (t.perm p.val.1)↔¬s.perm (t.perm p.val.1)<s.perm (t.perm p.val.2):= ⟨fun h=>not_lt_of_gt h,fun h=>lt_of_le_of_ne (le_of_not_gt h) hp.symm⟩
    unfold glyphO; simp only [Signed.mul_perm_apply, hue_mul,took,tw]; by_cases h:t.perm p.val.1< t.perm p.val.2 <;> by_cases hh:s.perm (t.perm p.val.1)<s.perm (t.perm p.val.2)<;> simp only [h,hh,he,↓reduceDIte,↓reduceIte,not_true,not_false_eq_true]<;> ring
lemma gross_s (x:Cover): gross (s.act x)=Ortho.motion s.ortho (gross x):=by
     ext i; obtain ⟨i,rfl⟩:=s.perm.surjective i; rw [Ortho.motion_at, Signed.ortho_move]; change (↑(s.act x (s.perm i)):ℝ) = s.act _ (s.perm i); rw [Signed.act_at,Signed.act_at]; split <;> simp [gross,Work.G03.castPos]
lemma sst : s.act (step a:Cover)= if s.flip a then -(step (s.perm a)) else step (s.perm a):=by ext i; obtain ⟨i,rfl⟩:=s.perm.surjective i; by_cases h:i=a <;> by_cases he:s.flip a=true <;> simp [Signed.act,h,he]
lemma crass : Ortho.motion s.ortho (basis a)=hue s a • basis (s.perm a):=by
     ext i; obtain ⟨i,rfl⟩:=s.perm.surjective i; rw [Ortho.motion_at,Signed.ortho_move]; by_cases h:i=a <;> simp [hue,YM.basis,Signed.act,h,Ne.symm,smul_ite] <;> split<;> simp_all
lemma gross_plus (x y:Cover): gross (x+y)=gross x+gross y:=by ext i; simp [gross, Work.G03.castPos]
lemma grosses : gross (dent s a)= if s.flip a then -(basis (s.perm a)) else 0:=by unfold dent; cases s.flip a <;> simp only [↓reduceIte,Bool.false_eq_true] <;> ext i<;> simp [gross,Work.G03.castPos,YM.basis,eq_comm]
-- change vars smooth
section Int
lemma changeA (b:Bool)(f:ℝ→F): (∫ x in (0:ℝ)..1, f (if b then 1-x else x))= ∫ x in (0:ℝ)..1,f x:=by cases b with|false=>simp|true=> simp only [if_true]; rw [intervalIntegral.integral_comp_sub_left]; simp
lemma swapA (f:ℝ→ℝ→F)(h:Continuous (uncurry f)): (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,f x y)=(∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, f x y):=by
    let I:=Set.Ioc (0:ℝ) 1; let μ:= volume.restrict I; let J:=Set.Icc (0:ℝ) 1
    have hf:IntegrableOn (uncurry f) (J×ˢ J) (volume.prod volume):= h.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    have he:IntegrableOn (uncurry f) (I×ˢI) (volume.prod volume):=hf.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
    rw [IntegrableOn,← Measure.prod_restrict] at he; simp_rw [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]; exact MeasureTheory.integral_integral_swap he
lemma peaks (X:E4)(v:ℝ): v • (Ortho.motion s.ortho (basis a))= gross (dent s a)+(if s.flip a then 1-v else v) • basis (s.perm a):=by
    rw [crass,grosses]; unfold hue; split; next h=>rw [neg_one_smul,smul_neg,sub_smul,one_smul]; abel
    next h=>simp_all
lemma playTurn (f:E4→F)(h: Continuous f)(q:Option PlaqAxes) : zoom q (f ∘ Ortho.motion s.ortho) (gross x)= zoom (q.map (took s)) f (gross (s.act x+porch s q)):=by
    cases q with
    | none=>unfold porch; simp [gross_s,zoom]
    | some p=> let i:=s.perm p.val.1; let j:=s.perm p.val.2; let a:=p.val.1; let b:=p.val.2; let u:=s.act x+porch s (.some p); let F(v w:ℝ):= f (gross u+(v • basis i+w • basis j))
               have he(v w:ℝ):f (Ortho.motion s.ortho (gross x+(v•basis a+w • basis b)))=F (if s.flip a then 1-v else v) (if s.flip b then 1-w else w):=by
                   unfold F; apply congr_arg f; unfold u; rw [show porch s (.some p)=_ from (show porch s (.some p)=dent s a+dent s b from rfl),gross_plus,gross_s, gross_plus,map_add,map_add,map_smul,map_smul]; rw [peaks s a 0 v,peaks s b 0 w]; dsimp only [a,b,i,j]; abel
               change (∫ v in (0:ℝ)..1,∫ w in (0:ℝ)..1,f (Ortho.motion s.ortho (gross x+(v•basis a+w • basis b))))=ameet (tw i j _) f (gross u); simp_rw [he,changeA (s.flip b) _]; rw [show (∫ v in (0:ℝ)..1,∫ w in (0:ℝ)..1, F (if s.flip a then 1-v else v) w) = ∫ v in (0:ℝ)..1,∫ w in (0:ℝ)..1,F v w from changeA (s.flip a) (fun v=>∫ w in (0:ℝ)..1,F v w)]; unfold tw; split
               next hp=>rfl
               next hp=> rw [swapA F (h.comp (show Continuous fun t:ℝ×ℝ=> gross u+(t.1 • basis i+t.2 • basis j) by fun_prop))]; unfold ameet F; simp_rw [show ∀ s r:ℝ,r • basis i+s • basis j=s • basis j+r • basis i from fun s r=> add_comm _ _]
end Int
end YM.Arise
#print axioms YM.Arise.playTurn
