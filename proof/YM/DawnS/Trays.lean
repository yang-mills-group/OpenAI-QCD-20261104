import YM.DawnS.Casks
set_option autoImplicit false
noncomputable section
namespace YM.DawnS
open Function Set Filter Finset Lattice Analysis MeasureTheory Tensor TensorProduct Maxwell Arise.Range Massive Massive.UV Massive.UV.Free QCD QCD.Lat Grass
open scoped Topology ContDiff BigOperators InnerProductSpace TensorProduct Classical Matrix
local notation "K"=> timeAxis
local notation "I₀"=>Complex.I
local notation "P"=> RingS
local notation "Ω"=>muS
variable {d:ℕ}
local notation "KK" d:arg r:arg => chime (fun _ : Fin 2 => d) (dotsG r)
set_option quotPrecheck false
variable (p q:chit d) (a b:Pinor) (i j:Hue) (k t:Flavor 6)(r:ℝ)(hr:0<r)
local notation "A"=>((p.val,a,i),k)
local notation "N"=> ((q.val,b,j),t)
local notation "η"=> sigL (d:=d) r
local notation "fP"=>lantern
local notation "Lp"=> listP p
local notation "Lq"=> listP q
local notation "G"=> rayG r ((listP p).length+(listP q).length+1)
include hr
lemma rows(pv:E4)(e:E4)(s v:ℝ)(ht0:pv-e=prelude s)(hs:|s|=r)(hv:s=v*r) : leg A ((q.val,b,i),k) pv e= rayG r ((listP p).length+(listP q).length+1) * (∫ z:P, phaseG p false z * phaseG q true z * shine v z a b ∂muS):=by
    unfold leg; simp only [and_self,if_true]; rw[ht0]; simp_rw[running]; rw [show toAxes Lp++toAxes Lq= toAxes (Lp++Lq) by simp[toAxes]]; let l:= Lp++Lq; let H(z:P):ℂ := (↑(stepTheta z l):ℂ)*shine v z a b; change _* deriveL (toAxes l) _ (prelude s) = _
    rw[spinC hr hs hv l a b]; let i':= (listP p).length; let j':= (listP q).length; let f:= G; rw [show l.length=i'+j' by simp[i',j',l]]; change (-1:ℂ)^ (toAxes Lq).length*((f:ℂ)*I₀^(i'+j')*(∫ z:P,H z ∂muS)) = ↑f*_ -- name f uses lean binder Fin.
    have he(z:P) : phaseG p false z *phaseG q true z* shine v z a b=(((-1:ℂ)^j')*I₀^(i'+j'))*H z:=by
             unfold phaseG H; rw [stepTheta_g]; simp only [Complex.ofReal_mul,↓reduceIte,Bool.false_eq_true]; unfold i' j'; rw [pow_add,show -I₀=(-1)*I₀ by ring,mul_pow (-1:ℂ)]; ring
    simp_rw [he]; rw [integral_const_mul, show (toAxes Lq).length=j' from List.length_map ..]; ring
lemma inColor : η (upL A) (upL N) = if i=j ∧ k=t then G * ∫ z:P, star (phaseG p false z) * phaseG q false z * lampS false z a b ∂Ω else 0:=by
    rw [cusp p q a b i j k t r hr]; by_cases h:i=j ∧ k=t; swap; · rw[if_neg h]; simp [UV.Free.leg, (fun he=> show False from h ((show (j=i∧t=k) from he).imp Eq.symm Eq.symm))] <;> tauto -- binder solve later
    obtain ⟨rfl,rfl⟩:=h; simp only [and_self,if_true];
    let X(z:P):ℂ:= star (phaseG p false z)*phaseG q false z
    let Y (s:Pinor)(z:P):= X z* shine 1 z b s
    have hV(s: Pinor): Free.leg ((q.val,b,i),k) ((p.val,s,i),k) (prelude r) 0= ↑G* ∫ z:P,Y s z ∂Ω :=by
         rw [rows q p b s i k r hr (prelude r) 0 r 1 (sub_zero _) (abs_of_pos hr) (one_mul _).symm, add_comm (listP q).length]; apply congr_arg; refine integral_congr_ae (Eventually.of_forall fun z=>?_); change _* shine _ _ _ _= X z*shine _ _ _ _; unfold X phaseG; simp [Complex.conj_I] <;> ring_nf <;> tauto
    simp_rw [hV]; have ht(z:P): X z*lampS false z a b=∑ s:Pinor,gamma K s a*Y s z:=by
          unfold lampS; simp only [Bool.false_eq_true,↓reduceIte,Matrix.transpose_apply,Matrix.mul_apply,Finset.mul_sum]; refine Finset.sum_congr rfl fun s _=>?_ ; unfold Y; ring
    change _=(G:ℂ)*∫ z:P,X z*lampS false z a b ∂Ω
    simp_rw [ht]; rw[integral_finsetSum]; simp_rw[integral_const_mul]; rw[Finset.mul_sum]; exact Finset.sum_congr rfl fun s _=>mul_left_comm ..
    intro i h; exact ((show Continuous (fun z:P=>gamma K i a*Y i z) from (continuous_const.mul ((((fluidG p false).star.mul (fluidG q false)).mul (shines 1 b i)))))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma barColor : η (dnL A) (dnL N) = if i=j ∧ k=t then G * ∫ z:P, star (phaseG p true z) * phaseG q true z * lampS true z a b ∂Ω else 0:=by
    rw [cape p q a b i j k t r hr]; by_cases h:i=j ∧ k=t; swap; · rw[if_neg h]; simp [UV.Free.leg, (fun he=> show False from h ((show (i=j∧k=t) from he).imp id id))] <;> tauto -- binder solve later
    obtain ⟨rfl,rfl⟩:=h; simp only [and_self,if_true];
    let X(z:P):ℂ:= star (phaseG p true z)*phaseG q true z
    let Y (s:Pinor)(z:P):= X z* shine (-1) z s b
    have hV(s: Pinor): Free.leg ((p.val,s,i),k) ((q.val,b,i),k) 0 (prelude r)= ↑G* ∫ z:P,Y s z ∂Ω :=by
         rw [rows p q s b i k r hr 0 (prelude r) (-r) (-1) (by simp [prelude]) (by simp [abs_of_pos hr]) (by simp)]; apply congr_arg; refine integral_congr_ae (Eventually.of_forall fun z=>?_); change _* shine _ _ _ _= X z*shine _ _ _ _; unfold X phaseG; simp [Complex.conj_I] <;> ring_nf <;> tauto
    simp_rw [hV]; have ht(z:P): X z*lampS true z a b=∑ s:Pinor,(-gamma K a s)*Y s z:=by
          unfold lampS; simp only [Bool.false_eq_true,↓reduceIte,Matrix.neg_apply, mul_neg, ← sum_neg_distrib,Matrix.mul_apply,Finset.mul_sum]; refine Finset.sum_congr rfl fun s _=>?_ ; unfold Y; ring
    change _=(G:ℂ)*∫ z:P,X z*lampS true z a b ∂Ω
    simp_rw [ht]; rw[integral_finsetSum]; simp_rw[integral_const_mul]; rw[Finset.mul_sum]; exact Finset.sum_congr rfl fun s _=>mul_left_comm ..
    intro i h; exact ((show Continuous (fun z:P=>(-gamma K a i)*Y i z) from (continuous_const.mul ((((fluidG p true).star.mul (fluidG q true)).mul (shines (-1) i b)))))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
end YM.DawnS
