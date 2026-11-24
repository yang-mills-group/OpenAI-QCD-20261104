import YM.QCD.Stew.October
/-! # Spin scalar and vector projection. chir readers make signed aggregates real. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
open Revolve Flume Quarry AnalyticBridge.VerifiedReset

def axisR (i:Axis): Signed:=⟨Equiv.refl _, fun p=>decide (p ≠ i)⟩
lemma axisControl (i:Axis): Swing (axisR i) (Lat.gamma i):=by
    refine ⟨⟨by simp,by simp⟩,fun p=>?_⟩; by_cases hp:i=p; · subst p; simp [axisR]
    simp [axisR,hp,Ne.symm hp, Lat.clifford hp]
-- full invariant sheet spectrum constrained by all permutations
structure Poem (W: SampleX→Spike):Prop where
 cycle (p s k)(h:Swing s k): W (tide s p)=skySig s p • (k*W p*star k)
 read i: W (invert i)=g5*star (W i)*g5

def muVal (W:SampleX→Spike):ℂ:= W none (0,0) (0,0)
def sineVal (W:SampleX→Spike)(i:Axis)(b:Bool):ℂ:= (Lat.gamma i*W (some (i,b))) (0,0) (0,0)
def qMass (W: SampleX→Spike):ℝ:=(muVal W).re
def qWave (W:SampleX→Spike):ℝ:= (sineVal W 0 true-sineVal W 0 false).re
lemma real_val (x:ℂ)(h:star x=x):x=(x.re:ℂ):=by
    apply Complex.ext; · simp
    have hp:=congr_arg Complex.im h; simp only [show star x=(starRingEnd ℂ) x from rfl, Complex.conj_im] at hp; simp only [Complex.ofReal_im]; linarith
variable {W:SampleX→Spike}(h:Poem W)
include h
lemma muse : W none=(qMass W:ℂ) • (1:Spike):=by
    let U:= W none; have he:U=muVal W • 1:=by
       apply scalar_spin; intro i; have hh:=h.cycle none _ _ (axisControl i); change U=(1:ℂ) • (Lat.gamma i*_ * _ ) at hh; rw [one_smul,gamma_star] at hh; change U*_ = _; let A:=Lat.gamma i; have he : U*A=A*U:=by nth_rw 1 [hh]; rw [Matrix.mul_assoc (A*_), gamma_sq, Matrix.mul_one] -- U unfolds?
       exact he
    let x:= muVal W; have hp : x= (x.re:ℂ):=by
       apply real_val; have hh:=h.read none; change U=g5*star U*g5 at hh; rw [he,star_smul,star_one,Matrix.mul_smul,mul_one,Matrix.smul_mul,g5_sq] at hh; exact Eq.symm (by simpa only [Matrix.smul_apply,Matrix.one_apply_eq, smul_eq_mul,mul_one] using Matrix.ext_iff.mpr hh (0,0) (0,0))
    exact he.trans (congr_arg (· • (1:Spike)) hp)
lemma waves (i:Axis)(u: Bool): W (some (i,u))=sineVal W i u • Lat.gamma i :=by
    let A:= Lat.gamma i; let v:=W (some (i,u))
    have ht:A*v= sineVal W i u • 1:=by
       apply scalar_spin; intro j
       let B:=Lat.gamma j; have hh:=h.cycle (some (i,u)) _ _ (axisControl j)
       rw [show tide (axisR j) (some (i,u))=some (i,u) by rfl, gamma_star] at hh; by_cases hj:i=j
       · subst j; change v=skySig _ _ • (A*v*A) at hh; rw [show skySig _ _=1 from ?_,one_smul] at hh; rotate_left; · simp [skySig,axisR]
         have he : v*A=A*v:= by nth_rw 1 [hh]; rw [Matrix.mul_assoc (A*v),gamma_sq,mul_one]
         exact Commute.mul_left (Commute.refl _) he
       have hk : skySig (axisR j) (some (i,u)) = -1 :=by simp [skySig,axisR,hj]
       change v=skySig _ _ • (B*v*B) at hh; rw [hk,neg_one_smul] at hh
       have he: v*B=-(B*v):=by nth_rw 1 [hh]; rw [Matrix.neg_mul, Matrix.mul_assoc (B*v),gamma_sq,mul_one]
       change A*v*B=B*(A*v); rw [Matrix.mul_assoc, he, Matrix.mul_neg, ← Matrix.mul_assoc, show A*B=_ from Lat.clifford hj]; simp [A,B,Matrix.mul_assoc]
    have hp:v=sineVal W i u • A:=by
       have hh:=congr_arg (A*·) ht; rw [← Matrix.mul_assoc, gamma_sq,one_mul,Matrix.mul_smul,mul_one] at hh; exact hh
    exact hp
lemma valid_wave (u:Bool)(i j:Axis): sineVal W j u=sineVal W i u :=by
    let s:= Swing.pure (Equiv.swap i j); obtain ⟨k,hk⟩:=Swing.goes s
    have he:s.perm i=j:=Equiv.swap_apply_left ..
    have hh:=h.cycle (some (i,u)) s k hk
    have hx : tide s (some (i,u))=some (j,u):=by change some (s.perm i,u)=_; rw [he]
    rw [hx,show skySig s _=(1:ℂ) from rfl,one_smul, waves h,waves h, Matrix.mul_smul, Matrix.smul_mul] at hh -- syntax
    have hz : k*Lat.gamma i*star k= Lat.gamma j:=by rw [hk.sends,he]; change Lat.gamma j*k*star k=_; rw [Matrix.mul_assoc,hk.unit.2,mul_one]
    rw [hz] at hh; have hd:=congr_arg (·*Lat.gamma j) hh; simp_rw [Matrix.smul_mul,Lat.gamma_sq] at hd
    simpa only [Matrix.smul_apply,Matrix.one_apply_eq, smul_eq_mul,mul_one] using Matrix.ext_iff.mpr hd (0,0) (0,0)
lemma reality (i:Axis): sineVal W i true - sineVal W i false=(qWave W:ℂ):=by
    rw [valid_wave h true 0, valid_wave h false 0]; apply real_val; let A:=Lat.gamma 0
    have hr:= h.read (some (0,false)); change W (some (0,true))=_ at hr
    rw [waves h,waves h,star_smul,gamma_star, Matrix.mul_smul, Matrix.smul_mul, show g5*A*g5= -A from ?_,smul_neg,← neg_smul] at hr; swap; · rw [show g5*A=-(A*g5) from (by rw [five,neg_neg]),Matrix.neg_mul,Matrix.mul_assoc,g5_sq,Matrix.mul_one]
    let z:= sineVal W 0 false; let p:=sineVal W 0 true; have hx:p = -star z:=by have hx:=congr_arg (·*A) hr; simp only [Matrix.smul_mul,A, gamma_sq] at hx; simpa only [Matrix.smul_apply,Matrix.one_apply_eq, smul_eq_mul,mul_one] using Matrix.ext_iff.mpr hx (0,0) (0,0) -- layout
    change star (p-z)=p-z; rw [hx,star_sub,star_neg,star_star]; abel
omit h
lemma stream (X:Spike) (q:ℂ) (a :Axis)(U:Grid c)(p:Spike): Commute (delta U a) (onSpin c p):=Δ_spins ..
lemma cores (o:Site c)(U:Grid c)(X:Spike)(a:SampleX)(q:ℂ): entry o (q • X) a U= q • entry o X a U:=by
    rcases a with _|⟨s,_|_⟩ <;> simp only [entry, Option.elim_none,Option.elim_some,Bool.false_eq_true,↓reduceIte,pineS, Matrix.mul_smul, Matrix.smul_mul]
lemma volley (X : Spike)(c:Side):(∑ i:Site c,localX i X)=onSpin c X:=by
    ext ⟨i,a⟩ ⟨j,b⟩; rw [Matrix.sum_apply]; by_cases h: i=j
    · subst j; rw [sum_eq_single i]; · simp [localX,onSpin,rides]
      · intro z _ hz; simp [localX,rides,hz]
      simp
    simp [localX,onSpin,rides,h]
def freeSpin (U:Grid c):Sheet c:= ∑ i:Axis, onSpin c (Lat.gamma i)*delta U i
include h
lemma total (U:Grid c):(∑ o: Site c,∑ s:SampleX, entry o (W s) s U)= (qMass W:ℂ) • 1+(qWave W:ℂ) • freeSpin U:=by
    rw [sum_comm,Fintype.sum_option,muse h]; change (∑ x:Site c,localX x _ )+ (∑ i,∑ x:Site c, entry x (W _) _ U)=_
    simp_rw [pineS]; rw [← Finset.smul_sum,volley,on_spin_one, Fintype.sum_prod_type]; unfold freeSpin; rw [Finset.smul_sum]; apply congr_arg
    refine sum_congr rfl fun i _=>?_ ; rw [Fintype.sum_bool]
    simp_rw [waves h]; simp only [entry,Option.elim,Bool.false_eq_true,↓reduceIte,Matrix.smul_mul, ← Matrix.sum_mul, ← Matrix.mul_sum, pineS,← Finset.smul_sum,volley]; -- inspect
    rw [Matrix.mul_smul,Matrix.neg_mul, (Δ_spins ..).eq, ← reality h i,sub_smul,smul_neg,sub_eq_add_neg]
end YM.QCD.Stew
