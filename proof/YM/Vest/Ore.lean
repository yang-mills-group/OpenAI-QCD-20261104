import YM.Vest.Key
set_option autoImplicit false
noncomputable section
namespace YM.Vest
open Function
open scoped BigOperators ContDiff Classical
open QCD QCD.Creek QCD.Bera QCD.Anomaly QCD.Grass QCD.Cove Finset Next.Rank Next.Rank.Normal
variable {A B C D U V X Y Z I:Type}[Fintype A][Fintype B][Fintype C][Fintype D][Fintype U][Fintype V][Fintype X][Fintype Y][Fintype Z][Fintype I]
open Matrix
variable {P H:Matrix A B ℂ}{Q V:Matrix B C ℂ}{M G : Matrix C D ℂ}{T E:Matrix B D ℂ}{x y z y' z' v e s t:ℝ}
private lemma coat (h:bills P univ x)(hg:bills Q univ y)(he:0≤y): bills (P*Q) univ (x*y):=by
   intro i _; simp only [Matrix.mul_apply]; refine ((sum_le_sum (fun j _=> (norm_sum_le ..))).trans ?_); rw [sum_comm]; simp_rw [norm_mul,← Finset.mul_sum]; exact (sum_le_sum (fun j _=> mul_le_mul_of_nonneg_left (hg j (mem_univ j)) (norm_nonneg _))).trans (by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (h i (mem_univ i)) he)
private lemma dent (h:bills P univ x)(he:bills H univ y): bills (P+H) univ (x+y):=by intro i hi; refine (sum_le_sum (fun j _=>norm_add_le ..)).trans ?_; rw [sum_add_distrib]; exact add_le_add (h i hi) (he i hi)
private lemma scale (h:bills P univ x)(he:∀ i j, ‖Q i j‖≤y)(hy:0≤y):∀ i j, ‖(P*Q) i j‖ ≤ x*y:= by intro i j; rw [Matrix.mul_apply]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun k=>‖P i k‖*y) (fun k _=> (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left (he k j) (norm_nonneg _)))).trans ?_); rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (h i (mem_univ _)) hy
private lemma prime {W:Matrix D C ℂ}(h:bills P univ x)(he:∀ i j,‖Q i j‖≤y)(hp:bills W univ z)(hx:0≤x)(hy:0≤y):∀ i j, ‖(P*Q*W.transpose) i j‖ ≤ (x*y)*z:=by
   intro i j; rw [Matrix.mul_apply]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun k=> (x*y)*‖W j k‖) (fun k _=>?_)).trans ?_)
   · rw [Matrix.transpose_apply,norm_mul]; exact mul_le_mul_of_nonneg_right (scale h he hy ..) (norm_nonneg _)
   rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hp j (mem_univ _)) (mul_nonneg hx hy)
private lemma gust (h:bills P univ x)(hp:bills V univ y)(hv:bills (P-H) univ v)(he:bills (Q-V) univ e)(hy:0 ≤ y)(he':0 ≤ e): bills (P*Q-H*V) univ (v*y+x*e):=by
    rw [show P*Q-H*V=(P-H)*V+P*(Q-V) from by rw [Matrix.sub_mul,Matrix.mul_sub]; abel]; exact dent (coat hv hp hy) (coat h he he')
private lemma gustY {Q V:Matrix B B ℂ}(h:bills P univ x)(hp:bills H univ x)(he:∀ i j,‖Q i j‖≤y)(he':∀ i j,‖V i j‖≤y)(hs:bills (P-H) univ v)(hG:∀ i j, ‖(Q-V) i j‖≤e)(h0:0 ≤ x)(h1:0 ≤y)(h2:0 ≤ v)(h3:0 ≤e):∀ i j, ‖(P*Q*P.transpose-H*V*H.transpose) i j‖ ≤ v*y*x+x*e*x+x*y*v:=by
   intro i j; rw [show P*Q*P.transpose-H*V*H.transpose=(P-H)*Q*P.transpose+ H*(Q-V)*P.transpose+ H*V*(P-H).transpose from by simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.transpose_sub]; abel,Matrix.add_apply, Matrix.add_apply]; exact (norm_add_le _ _).trans (add_le_add ((norm_add_le ..).trans (add_le_add (prime hs he h h2 h1 ..) (prime hp hG h h0 h3 ..))) (prime hp he' hs h0 h1 ..))
namespace Tone
variable {T T': Tone A X B Y}{S S': Tone B Y C Z}
abbrev Rich (T:Tone A X B Y)(x:ℝ) := Sky T.P T.Q T.M T.V univ univ x x x x
abbrev Gale (T T' :Tone A X B Y)(x:ℝ):= drifts T.P T.Q T.M T.V T'.P T'.Q T'.M T'.V univ univ x
def amount (x:ℝ):=10*x^2
lemma lacks (hp:1 ≤ x): 1≤amount x:= one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hp)
private lemma bills_up (h:bills P univ x)(hp:x ≤v): bills P univ v:= fun i hi=> (h i hi).trans hp
private lemma tonne {A:Type}[Fintype A]{Q:Next.Rank.Normal.Symmetric A} : Pane Q univ z ↔ ∀ i j,‖Matrix.of Q.cov i j‖≤z:= ⟨fun h i j=>h i (mem_univ i) j (mem_univ _),fun h i _ j _=> h i j⟩
lemma refreshRich (h:Rich T x)(hv:Rich S y): Rich (T.after S) (amount x*y) :=by
   have hx:=h.craze; have hp:= hv.craze; have hy:=h.heel; have he:=hv.heel; have hz: 1 ≤ amount x*y:=one_le_mul_of_one_le_of_one_le (lacks hx) hp; have hA:= mul_le_mul_of_nonneg_left hp hy; have hB:= le_mul_of_one_le_left (mul_nonneg hy he) hx
   have h1:x*y≤ amount x*y:= by unfold amount; nlinarith only [hB,mul_nonneg hy he]
   have h2:x*y*x+x≤amount x*y:=by unfold amount; nlinarith only [hB,hA,mul_nonneg hy he]
   refine ⟨hz,zero_le_one.trans hz,hz,zero_le_one.trans hz,bills_up (coat h.gu hv.gu he) h1,tonne.mpr ?_,bills_up (coat h.po hv.po he) h1,fun i hi j hj=>?_⟩
   · intro i j; unfold after; dsimp only; rw [camped,scalM, Matrix.add_apply]; refine (norm_add_le ..).trans ((add_le_add (prime h.gu (tonne.mp hv.sec) h.gu hy he ..) ((tonne.mp h.sec) i j)).trans h2)
   unfold after; dsimp only; rw [Matrix.add_apply]; refine (norm_add_le ..).trans ((add_le_add (prime h.po (fun i j=>hv.trib i (mem_univ _) j (mem_univ j)) h.po hy he ..) (h.trib i hi j hj)).trans h2)
lemma growGale (h:Rich T x)(h':Rich T' x)(hp:Rich S y)(hp':Rich S' y)(he:0 ≤ e) (hx:Gale T T' e)(hY:Gale S S' (e*y)): Gale (T.after S) (T'.after S') (e*(amount x*y)) :=by
    have hs:= h.craze; have hv:=hp.craze; have h0:=h.heel; have h1:=hp.heel; have ht:0≤e*y:=mul_nonneg he hp.heel; have hz:= le_mul_of_one_le_left ht hs; have h4:= le_mul_of_one_le_left (mul_nonneg h0 ht) hs; have h5:= le_mul_of_one_le_right he hv
    have h2:e*y+x*(e*y)≤e*(amount x*y):=by unfold amount; nlinarith only [hz,h4,ht]
    have h3:e*y*x+x*(e*y)*x+x*y*e+e ≤ e*(amount x*y):=by unfold amount; nlinarith only [hz,h4,h5,ht]
    refine ⟨bills_up (gust h.gu hp'.gu hx.G₀ hY.G₀ h1 ht) h2, tonne.mpr ?_, bills_up (gust h.po hp'.po hx.V₀ hY.V₀ h1 ht) h2,?_⟩
    · have h'₁ i j: ‖(Matrix.of S.Q.cov-Matrix.of S'.Q.cov) i j‖≤e*y:= by
         convert (tonne.mp hY.G₁ i j) using 2; exact sub_eq_add_neg ..
      intro i j
      have ht' i j: ‖(Matrix.of T.Q.cov-Matrix.of T'.Q.cov) i j‖≤e := by convert (tonne.mp hx.G₁ i j) using 2; exact sub_eq_add_neg ..
      rw [show Matrix.of ((T.after S).Q+-(T'.after S').Q).cov= T.P*Matrix.of S.Q.cov*T.P.transpose-T'.P*Matrix.of S'.Q.cov*T'.P.transpose+(Matrix.of T.Q.cov-Matrix.of T'.Q.cov) from ?_,Matrix.add_apply]; swap
      · unfold after; dsimp only; rw [←scalM,←scalM, camped,camped,show (Matrix.of (-(scope (spool T'.P) S'.Q+T'.Q)).cov) = -(Matrix.of (scope (spool T'.P) S'.Q+T'.Q).cov) from rfl, camped]; abel
      exact (norm_add_le ..).trans ((add_le_add (gustY h.gu h'.gu (tonne.mp hp.sec) (tonne.mp hp'.sec) hx.G₀ h'₁ h0 h1 he ht ..) (ht' i j)).trans h3)
    intro i hi j hj
    have hz:=gustY h.po h'.po (Q:=S.V) (V:=S'.V) (fun i j=>hp.trib i (mem_univ i) j (mem_univ j)) (fun i j=>hp'.trib i (mem_univ i) j (mem_univ j)) hx.V₀ (fun i j=>hY.V₁ i (mem_univ i) j (mem_univ j)) h0 h1 he ht i j
    rw [← Matrix.sub_apply,show (T.after S).V-(T'.after S').V=(T.M*S.V*T.M.transpose-T'.M*S'.V*T'.M.transpose)+(T.V-T'.V) from by unfold after; dsimp only; abel,Matrix.add_apply]; exact (norm_add_le ..).trans ((add_le_add hz (show ‖(T.V-T'.V) i j‖≤e from hx.V₁ i hi j hj)).trans h3)
lemma richMono (hp:1≤x) : Rich (monoT A X) x:= by
    have hv:=zero_le_one.trans hp; refine ⟨hp,hv,hp,hv,fun i _=>?_,fun i _ j _=>?_,fun i _=>?_,fun i _ j _=>?_⟩; all_goals simp [monoT, Matrix.one_apply,apply_ite (‖·‖)] <;> first|exact hp|exact hv|simpa only [show ‖((0:Next.Rank.Normal.Symmetric A).cov _ _)‖=0 from norm_zero] using hv
lemma calmGale (hp:0≤x): Gale T T x:=by refine ⟨fun i _=>?_,fun i _ j _=>?_,fun i _=>?_,fun i _ j _=>?_⟩; all_goals first|simpa using hp|simpa only [Next.Rank.Normal.Symmetric.cancels,show ‖(0:Next.Rank.Normal.Symmetric A).cov i j‖=0 from norm_zero] using hp
end Tone
end YM.Vest

#print axioms YM.Vest.Tone.growGale
