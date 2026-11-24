import YM.Bank.Merchant
import YM.QCD.Pearl.Culp
set_option autoImplicit false
noncomputable section
namespace YM.Bank.Wale
open Function Lattice Laurent Bloch Matrix Metric RG Work.F06 Filter Precision Finset
open Next.Free Exterior Learn Merchant
open scoped BigOperators Topology Matrix ComplexConjugate Matrix.Norms.L2Operator
variable {X : Type*}[NormedAddCommGroup X] {ι ι' ρ : Type}[Fintype ι][DecidableEq ι][Fintype ι'][DecidableEq ι'][Fintype ρ][DecidableEq ρ] {D:Type*}[NormedRing D]{q: Momentum} {a b t x y:ℝ}
structure Twin (f g:X)(a b t:ℝ):Prop where
   shines : ‖f‖ ≤ a*b
   seems : ‖g‖ ≤ a*b
   fares : ‖f-g‖ ≤ a*b*t
lemma Twin.add {f h g k:X} (hp:Twin f g a b t)(hi:Twin h k x b t): Twin (f+h) (g+k) (a+x) b t:=by
    refine ⟨(norm_add_le ..).trans ((add_le_add hp.shines hi.shines).trans_eq (by ring)), (norm_add_le ..).trans ((add_le_add hp.seems hi.seems).trans_eq (by ring)), ?_⟩; rw [add_sub_add_comm,add_mul,add_mul]; exact (norm_add_le ..).trans (add_le_add hp.fares hi.fares)
lemma Twin.prod {f h:Matrix ι ρ ℂ}{g k:Matrix ρ ι' ℂ} (hp:Twin f h a b t)(hi:Twin g k x y t) : Twin (f*g) (h*k) (2*a*x) (b*y) t:=by
    have h0 :0 ≤ a*b:=(norm_nonneg f).trans hp.shines; have h1:0 ≤ x*y:=(norm_nonneg g).trans hi.shines
    have he : a*b*(x*y) ≤ 2*a*x*(b*y):=by nlinarith only [mul_nonneg h0 h1]
    refine ⟨(l2_opNorm_mul ..).trans ((mul_le_mul hp.shines hi.shines (norm_nonneg _) h0).trans he), (l2_opNorm_mul ..).trans ((mul_le_mul hp.seems hi.seems (norm_nonneg _) h0).trans he),?_⟩
    rw [show f*g-h*k=f*(g-k)+(f-h)*k by rw [Matrix.mul_sub,Matrix.sub_mul]; abel]; exact (norm_add_le ..).trans ((add_le_add ((l2_opNorm_mul ..).trans (mul_le_mul hp.shines hi.fares (norm_nonneg _) h0)) ((l2_opNorm_mul ..).trans (mul_le_mul hp.fares hi.seems (norm_nonneg _) ((norm_nonneg _).trans hp.fares)))).trans_eq (by ring))
lemma Twin.higher {f g:X} (hp:Twin f g a b t)(he:a≤ x)(hb:0≤ b)(ht:0 ≤ t): Twin f g x b t :=
     let hh:=mul_le_mul_of_nonneg_right he hb; ⟨hp.shines.trans hh, hp.seems.trans hh, hp.fares.trans (mul_le_mul_of_nonneg_right hh ht)⟩
lemma Twin.straight {f g:ℂ} (hp:Twin f g a b t): Twin (star f) (star g) a b t := by
     have hh: ‖star f-star g‖=‖f-g‖:=by rw [←star_sub,norm_star]
     constructor; rw [norm_star]; exact hp.shines; rw [norm_star]; exact hp.seems; rw [hh]; exact hp.fares
lemma Twin.ref {f g:Matrix ι ρ ℂ} (hp:Twin f g a b t):Twin fᴴ gᴴ a b t:=by
     have hh : ‖fᴴ-gᴴ‖=‖f-g‖:=by rw [←Matrix.conjTranspose_sub,l2_opNorm_conjTranspose]
     constructor; rw [l2_opNorm_conjTranspose]; exact hp.shines; rw [l2_opNorm_conjTranspose]; exact hp.seems; rw [hh]; exact hp.fares
lemma Twin.click {f g h k:ℂ}(hp:Twin f h a b t)(hi:Twin g k x y t): Twin (f*g) (h*k) (2*a*x) (b*y) t:=by
    have h0 :0 ≤ a*b:=(norm_nonneg f).trans hp.shines; have h1:0 ≤ x*y:=(norm_nonneg g).trans hi.shines
    have he : a*b*(x*y) ≤ 2*a*x*(b*y):=by nlinarith only [mul_nonneg h0 h1]
    refine ⟨(norm_mul_le ..).trans ((mul_le_mul hp.shines hi.shines (norm_nonneg _) h0).trans he), (norm_mul_le ..).trans ((mul_le_mul hp.seems hi.seems (norm_nonneg _) h0).trans he),?_⟩
    rw [show f*g-h*k=f*(g-k)+(f-h)*k by ring]; exact (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul hp.shines hi.fares (norm_nonneg _) h0)) ((norm_mul_le ..).trans (mul_le_mul hp.fares hi.seems (norm_nonneg _) ((norm_nonneg _).trans hp.fares)))).trans_eq (by ring))
lemma Twin.peek {f g:Matrix ι ρ ℂ}(hp: Twin f g a b t)(i j): Twin (f i j) (g i j) a b t:=⟨(QCD.Cost.north ..).trans hp.shines,(QCD.Cost.north ..).trans hp.seems,(QCD.Cost.north (f-g) ..).trans hp.fares⟩

-- symbol zero expansions

def barrier (p:Momentum)(l:List Axis):ℂ:= (l.map fun i=> Complex.I*p i).prod
def τ (p:Momentum)(n:ℕ):= wedge n fun i=> Complex.I * p i
lemma chip_one (hp:‖q‖ ≤ 1)(a:Axis):Twin (chip (q a)) (Complex.I*(q a)) 2 ‖q‖ ‖q‖:=by
   have ht:‖Complex.I*q a‖≤‖q‖:=by rw [norm_mul,Complex.norm_I,one_mul]; exact norm_le_pi_norm _ _
   have hs:= ht.trans hp
   have hh:‖q‖^2 ≤ ‖q‖:=by nlinarith[norm_nonneg q]
   have hm:‖chip (q a)-Complex.I*q a‖ ≤ ‖q‖^2 := (Complex.norm_exp_sub_one_sub_id_le hs).trans (pow_le_pow_left₀ (norm_nonneg _) ht 2)
   refine ⟨?_,by linarith [norm_nonneg q], hm.trans (by nlinarith [sq_nonneg ‖q‖])⟩; linarith [norm_sub_norm_le (chip (q a)) (Complex.I*q a)]
lemma chips (l:List Axis)(hp:‖q‖ ≤ 1) : Twin (listChip q l) (barrier q l) ((4:ℝ)^l.length) (‖q‖^l.length) ‖q‖:=by -- precedence!
   induction l with
   | nil=> constructor <;>simp [listChip,barrier]
   | cons a l ih=> unfold listChip barrier; rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,List.length_cons,pow_succ',pow_succ']; have hh:= (chip_one hp a).click ih; rw [show (2:ℝ)*2=4 by norm_num] at hh; exact hh
lemma sails (i:ℕ) :∃ E:ℝ,0≤E∧∀ q: Momentum,‖q‖≤1→Twin (signal 1 i q) (τ q i) E ‖q‖ ‖q‖:=by
   let f (i:ℕ)(a:Axis):= left ℂ i a
   suffices h:∀ s:Finset Axis, ∃ E:ℝ,0≤ E ∧∀ q:Momentum,‖q‖≤1→ Twin (∑ a∈s,chip (q a) • f i a) (∑ a∈s,(Complex.I*q a) • f i a) E ‖q‖ ‖q‖ by
        have he:=h univ; simpa only [τ,signal,wedge,tripQ,f,PNat.one_coe,Nat.cast_one,one_mul]
   intro s; induction s using Finset.induction_on with
   | empty=> exact ⟨0,le_rfl,fun q h=> by rw [sum_empty,sum_empty]; constructor<;>simp⟩
   | @insert a s ha ih=>
       obtain ⟨E,hE,H⟩:=ih
       refine ⟨2*‖f i a‖+E,by positivity,fun q hh=>?_⟩; rw [sum_insert ha,sum_insert ha]; refine Twin.add ?_ (H _ hh)
       obtain ⟨hX,hY,hZ⟩:= chip_one hh a; constructor <;> try rw [norm_smul]
       · exact (mul_le_mul_of_nonneg_right hX (norm_nonneg _)).trans_eq (by ring)
       · exact (mul_le_mul_of_nonneg_right hY (norm_nonneg _)).trans_eq (by ring)
       rw [←sub_smul,norm_smul]; exact (mul_le_mul_of_nonneg_right hZ (norm_nonneg _)).trans_eq (by ring)
-- metric real small & hol strip
variable {p: Row (TypeFace 2) (TypeFace 2)} {q': Momentum} {r:ℝ}
lemma hol_d (hp:p.strip r b)(h:0<r)(hz:q∈cube (r/2)): DifferentiableAt ℂ p.read q:=by
    apply ℳ.differentiableAt.comp q (f:=fun z=> of.symm (p.read z)); refine differentiableAt_pi.mpr fun i=> differentiableAt_pi.mpr fun j=>?_
    exact (Work.F07.readDeriv (p.constant_strip hp i j) (by linarith) (show r/2<r by linarith) hz.1).1
lemma holM (hp:p.strip r b)(h:0<r)(hb:0≤ b)(hz:q∈cube (r/2)): ‖p.read q‖ ≤ ‖ℳ‖*b :=by
   apply (ℳ.le_opNorm (of.symm (p.read q))).trans; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _);
   apply (pi_norm_le_iff_of_nonneg hb).mpr; intro i; apply (pi_norm_le_iff_of_nonneg hb).mpr; intro j; exact (p.constant_strip hp i j).estimate q fun i=> ((cube_mono (by linarith : r/2≤r) hz).1 i).le
lemma blouse (r b:ℝ)(hr:0<r)(hb:0≤b): ∃ E s:ℝ, 0≤ E∧0<s ∧ s≤1 ∧∀ (p:Row (TypeFace 2) (TypeFace 2)),p.strip r b→p.read 0=1→ ∀ q:Momentum,‖q‖≤s →Twin (p.read q) 1 E 1 ‖q‖:=by
   let s:= min 1 (r/4/4); have hs:0<s:=lt_min one_pos (by positivity); let C:= ‖ℳ‖*b
   have he:ball (0:Momentum) (r/4)⊆cube (r/2) := by
      have hx:0<r/4:=by positivity
      have hg:= ball_inside_cube (cube_zero (r/4) hx) (η:=r/2) -- names
      rw [show r/2-r/4=r/4 by ring] at hg; exact hg
   let E:=max C (C/(r/4/2))
   refine ⟨E,s,(mul_nonneg (norm_nonneg ℳ) hb).trans (le_max_left ..),hs,min_le_left ..,fun p h hm q hq=> ?_⟩
   have hx: q∈ball (0:Momentum) (r/4/2):=by rw [mem_ball,dist_zero_right]; have hh: s≤r/4/4:=min_le_right ..; linarith
   have hu:= QCD.Run.lastwig _ (show 0<r/4 by positivity) (fun i hi=> hol_d h hr (he hi)) (R:=C) (fun i hi=> holM h hr hb (he hi)) hx
   have ht (q : Momentum)(hy: q∈ball (0:Momentum) (r/4)): ‖p.read q‖ ≤ E*1 :=by rw [mul_one]; exact (holM h hr hb (he hy)).trans (le_max_left ..)
   rw [← hm]; rw [sub_zero] at hu
   exact ⟨ht q (ball_subset_ball (by linarith) hx),ht _ (mem_ball_self (by positivity)),hu.trans (mul_le_mul_of_nonneg_right ((le_max_right ..).trans_eq (mul_one E).symm) (norm_nonneg q))⟩
end YM.Bank.Wale
#print axioms YM.Bank.Wale.blouse
#print axioms YM.Bank.Wale.chips
#print axioms YM.Bank.Wale.sails
