import YM.QCD.Tide.Shed
/-! # intertwining Gaussian conditioning/insertion.
Use generator-order signs explicitly for adjunction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Function NormedSpace Finset Grass Creek Kit Matrix
open scoped BigOperators Matrix Topology Classical
variable {A B C M: Type*}[Fintype A][Fintype B][Fintype C][Fintype M]
variable [DecidableEq A][DecidableEq B]
variable (U:Matrix A A ℂ)(V:Matrix B B ℂ) (hU:U∈unitary _) (hV:V∈unitary _)
include hU hV
lemma ballroom (Q:Matrix A B ℂ):foam (U*Q*star V)=(whole U V)* foam Q*star (whole U V):=by
   rw [whole_star]; unfold foam whole; have hh : star U*U=1:=hU.1; have hx : U*star U=1:=hU.2
   simp only [Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add, neg_zero,Matrix.mul_one,Matrix.mul_neg,Matrix.neg_mul,Matrix.conjTranspose_mul,← Matrix.star_eq_conjTranspose U,← Matrix.star_eq_conjTranspose (star V),star_star,hx]
   congr 1
   rw [Matrix.mul_assoc] -- trial
   rw [Matrix.mul_assoc (V) _ _, Matrix.mul_assoc Qᴴ (star U), Matrix.mul_assoc U Q, ← Matrix.mul_assoc (star U) U,hh,Matrix.one_mul, ← Matrix.mul_assoc Qᴴ, ← Matrix.mul_assoc V (_*_) ]
lemma roofed (Q:Matrix A B ℂ)(x:Dirac A): disguise V (furnace (U*Q*star V) x)= furnace Q (disguise U x):=by
   rw [← mingler,← mingler,rotated_marginal hU hV, ballroom _ _ hU hV]; simp only [map_mul,disguised (whole_u _ _ hU hV),partitioned]
omit hU hV
lemma studio (x:Dirac A): tilt (whole U V) (near A B x)=near A B (tilt U x):=by
   refine LinearMap.congr_fun (ext_reversing (F:=(tilt (whole U V)).comp (near A B).toLinearMap) (G:=(near A B).toLinearMap.comp (tilt U)) (by simp [tilt_mul]) (by simp [tilt_mul]) (by simp) ?_) x
   rintro (i|i)
   · change tilt _ (near A B (psi i))=near A B (tilt _ (psi i)); rw [near,pass_psi,tilt_psi,tilt_psi]; simp [Fintype.sum_sum_type,whole]
   change tilt _ (near A B (bar i))=near A B (tilt _ (bar i)); rw [near,pass_bar,tilt_bar,tilt_bar]; simp [Fintype.sum_sum_type,whole]
lemma studies (x:Dirac B): tilt (whole U V) (far A B x)= far A B (tilt V x):=by
   refine LinearMap.congr_fun (ext_reversing (F:=(tilt (whole U V)).comp (far A B).toLinearMap) (G:=(far A B).toLinearMap.comp (tilt V)) (by simp [tilt_mul]) (by simp [tilt_mul]) (by simp) ?_) x
   rintro (i|i)
   · change tilt _ (far A B (psi i))=far A B (tilt _ (psi i)); rw [far,pass_psi,tilt_psi,tilt_psi]; simp [Fintype.sum_sum_type,whole]
   change tilt _ (far A B (bar i))=far A B (tilt _ (bar i)); rw [far,pass_bar,tilt_bar,tilt_bar]; simp [Fintype.sum_sum_type,whole]
-- sign after tilting: only even contributions of A
lemma stole (x:Dirac A)(y:Dirac B): marginal A B (far A B y * near A B x)= marginal A B (near A B x*far A B y):=by
   let a:= plus x; let b:= minus x; let Z:=far A B
   have hh: Plus (near A B a):= Eq.trans (pass_grade ..) (congr_arg _ (plus_grade x)); have hz : Minus (near A B b):= Eq.trans (pass_grade ..) ((congr_arg (near A B) (minus_grade x)).trans (map_neg ..));
   change marginal A B (Z y*_)=_; rw [← both x]; change marginal A B (far A B y*near A B (a+b))=_; rw [map_add (near A B)]; --
   change marginal A B (Z y*(near A B a+near A B b))= marginal A B ((near A B a+near A B b)*Z y)
   rw [mul_add,add_mul,map_add,map_add, (hh.central (Z y)).eq, hz.slides (Z y),show grade (Z y)= far A B (grade y) from pass_grade ..]; rw [margins A B b (grade y),show marginal A B (near A B b*Z y)=_ from margins A B b y,odd_loss (minus_grade x)]; simp
-- tilted trace
variable (hp:star U=U)(hs:U*U=1)(hh:star V=V)(hr:V*V=1)
include hp hs hh hr
lemma studied (x:Dirac (A ⊕ B)): tilt V (marginal A B x)= marginal A B (tilt (whole U V) x):=by
   have hv(a:Dirac A)(b:Dirac B): tilt V (marginal A B (near A B a*far A B b))= marginal A B (tilt (whole U V) (near A B a*far A B b)):=by
       rw [margins,tilt_mul,studio,studies,stole,margins,tilt_amp _ hs,map_smulₛₗ]; rfl
   rw [← write x,map_sum,map_sum,map_sum,map_sum]; apply sum_congr rfl; intro i _; obtain ⟨a,b,he|he⟩:= split_mono A B i <;> simp only [he,map_smul,map_smulₛₗ,map_neg,hv]
omit hp hs hh hr in
lemma snow (Q:Matrix A B ℂ): star (foam Q)=foam Q:=by unfold foam; rw [Matrix.star_eq_conjTranspose]; simp [Matrix.fromBlocks_conjTranspose] -- test
lemma mintH (Q:Matrix A B ℂ): whole U V*(star (foam Q) * whole U V)=foam (U*Q*V):=by
    have he:= ballroom U V ⟨by rw [hp]; exact hs,by rw [hp]; exact hs⟩ ⟨by rw [hh]; exact hr,by rw [hh]; exact hr⟩ Q
    rw [whole_star,hp,hh,mul_assoc] at he; rw [he,snow]
omit hp hs hh hr in
lemma tiltingX {X Y:Matrix C C ℂ}(S:Matrix C C ℂ)(h:S*(star X*S)=Y) : tilt S (gauss X)=gauss Y:=by unfold gauss; rw [tilt_exp,tilt_form,h]
lemma frosts (Q: Matrix A B ℂ)(x:Dirac A): tilt V (furnace Q x)=furnace (U*Q*V) (tilt U x):=by
    have hy:U∈unitary _:=⟨by rw [hp]; exact hs, by rw [hp]; exact hs⟩ -- hp.symm ▸ not valid for hs multiple
    have hw:V∈unitary _:=⟨by rw [hh]; exact hr, by rw [hh]; exact hr⟩
    have ht (Q:Matrix A B ℂ): tilt (whole U V) (gauss (foam Q))=gauss (foam (U*Q*V)):= tiltingX _ (mintH _ _ hp hs hh hr Q)
    rw [← mingler, ← mingler, studied _ _ hp hs hh hr, tilt_mul,studio,ht, ((gauss_plus _).central _).eq] -- commute Eq
end YM.QCD.Tide
