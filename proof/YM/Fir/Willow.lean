import YM.Fir.Window
/-! All-axis finite mesh estimate from authentic one-step differences. -/
set_option autoImplicit false
noncomputable section
namespace YM.Fir
open Set Function Filter Metric
open scoped Topology
variable {I X F: Type*}[Fintype I] [DecidableEq I]
noncomputable abbrev imageF (a:ℝ)(p:I→ℤ): I→ℝ:= fun i=> a * p i
noncomputable abbrev markF (a:ℝ)(p:I→ℝ): I→ℤ:=fun i=> ⌊p i / a⌋
lemma extentF (x:I→ℝ){a:ℝ}(h:0<a): dist (imageF a (markF a x)) x ≤ a:=by
    refine (dist_pi_le_iff h.le).mpr (fun i=>?_); let y:=⌊x i/a⌋; have hx:= Int.lt_floor_add_one (x i/a); have hy:(y:ℝ) ≤ x i/a:= Int.floor_le _; change x i / a < ↑y+1 at hx; rw [div_lt_iff₀ h] at hx; rw [le_div_iff₀ h] at hy; rw [Real.dist_eq,abs_le]; change -a ≤ a*y-x i∧ a*y-x i ≤ a; constructor <;> linarith
lemma visible (x:I→ℝ){a:ℕ→ℝ}(hx:∀ i,0<a i)(h:Tendsto a atTop (𝓝 0)): Tendsto (fun i=>imageF (a i) (markF (a i) x)) atTop (𝓝 x):= Metric.tendsto_nhds.mpr fun ε hp=> (h.eventually_lt_const hp).mono fun i hi=> lt_of_le_of_lt (extentF _ (hx _)) hi
abbrev advanceF (b:I)(x:I→ℤ):= update x b (x b+1)
variable [MetricSpace X] (f:(I→ℤ)→ X)
namespace Mesh
variable {a r C:ℝ}{x:I→ℝ}(hr:0<r)(ha:0<a)(hq:0 ≤ C)(H:∀ (p:I→ℤ),imageF a p∈ball x r→∀ b:I,imageF a (advanceF b p)∈ball x r→ dist (f (advanceF b p)) (f p)≤ C*a)
include ha hr H
set_option maxHeartbeats 360000 in
lemma level (p:I→ℤ)(b:I)(n:ℕ): let q(k:ℕ):= update p b (p b+k); imageF a p∈ball x r → imageF a (q n)∈ball x r→ dist (f p) (f (q n))≤ n*(C*a) :=by
    let q(k:ℕ):=update p b (p b+k); have hq:q 0=p:= funext fun i=>by by_cases h:i=b; subst i; simp [q]; simp [q,h]
    intro _ hp hv; change imageF a (q n)∈ball x r at hv; have hu(k:ℕ)(hk:k≤n): imageF a (q k)∈ball x r:=by
        rw [ball_pi _ hr]; intro i hi; have hh:= (dist_pi_lt_iff hr).mp (Metric.mem_ball.mp hp) i; by_cases he:i=b
        · subst i; have h:= (dist_pi_lt_iff hr).mp (Metric.mem_ball.mp hv) b; simp only [imageF, Real.dist_eq, Function.update_self,mem_ball,abs_lt,q,Int.cast_add,Int.cast_natCast] at h hh ⊢ -- may loops
          have h0:0 ≤ (k:ℝ):=(by positivity); have hs:(k:ℝ)≤(n:ℝ):=(by exact_mod_cast hk); constructor <;> nlinarith
        rw [show imageF a (q k) i=imageF a p i from congr_arg (fun v:ℤ=>a*v) (update_of_ne he ..)]; exact Metric.mem_ball.mpr hh
    have hh(k:ℕ)(hk:k≤n): dist (f p) (f (q k))≤ k*(C*a):=by
        induction k with
        | zero=> simp [hq]
        | succ k ih=>
          have hs:q (k+1)=advanceF b (q k):=by unfold advanceF q; rw [update_self,update_idem]; simp [add_assoc]
          have hl:= H (q k) (hu _ (by omega)) b (hs ▸ (hu _ hk)); rw [←hs,dist_comm] at hl
          refine (dist_triangle _ (f (q k)) _).trans ((add_le_add (ih (by omega)) hl).trans_eq ?_); rw [Nat.cast_add,Nat.cast_one]; ring
    exact hh _ le_rfl
lemma upward (p t:I→ℤ)(b:I)(h:∀ i,i≠b→p i=t i)(h0:p b≤t b)(hp:imageF a p∈ball x r)(ht:imageF a t∈ball x r):dist (f p) (f t)≤ C*dist (imageF a p b) (imageF a t b):=by
     let v:ℤ:=t b-p b; have hv:0 ≤ v:= sub_nonneg.mpr h0; let n:=v.toNat; have he:(n:ℤ)=v:= Int.toNat_of_nonneg hv; have hh:update p b (p b+n)=t:=by
         funext i; by_cases hy:i=b; subst i; rw [update_self, he]; simp[v]; rw [update_of_ne hy]; exact h _ hy
     have hl:= level f hr ha H p b n hp (show imageF a (update p b (p b+n))∈ball x r from hh.symm ▸ ht); simp only [hh] at hl; refine hl.trans_eq ?_
     have hx:(n:ℝ)=(t b:ℝ)-↑(p b):= (by exact_mod_cast he: _) -- type?
     simp only [imageF,Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (mul_le_mul_of_nonneg_left (show (p b:ℝ) ≤ ↑(t b) from by exact_mod_cast h0) ha.le)),hx]; ring
include hq
lemma snake (p t:I→ℤ)(hp:imageF a p∈ball x r)(ht:imageF a t∈ball x r):dist (f p) (f t) ≤ (Fintype.card I)*(C*dist (imageF a p) (imageF a t)):=by
    -- piecewise path
    let X(s:Finset I)(i:I):ℤ:= if i∈s then t i else p i; let D:=C*dist (imageF a p) (imageF a t)
    have hy(s:Finset I): imageF a (X s)∈ball x r:=by
        rw [ball_pi _ hr]; intro i hi; unfold imageF X; split_ifs; · exact (ball_pi x hr ▸ ht) i hi -- cast?
        exact (ball_pi x hr ▸ hp) i hi
    have h(s:Finset I): dist (f p) (f (X s))≤ s.card*D:=by
        induction s using Finset.induction_on with
        | empty=> simp [show X ∅=p from by ext; simp[X]]
        | insert i s hi ih=>
          let u:= X s; let v:= X (insert i s)
          have hu:u i=p i:= if_neg hi; have hv:v i=t i:= if_pos (Finset.mem_insert_self ..)
          have hzi(j:I)(hj:j≠i):u j=v j:=by simp [u,v,X,hj]
          have hz:dist (f u) (f v) ≤ C*dist (imageF a u i) (imageF a v i):=by
               rcases le_total (u i) (v i) with h|h; exact upward f hr ha H u v i hzi h (hy _) (hy _)
               rw [dist_comm, dist_comm (imageF a u i)]; exact upward f hr ha H v u i (fun i h=> (hzi i h).symm) h (hy _) (hy _)
          have hm:(C*dist (imageF a u i) (imageF a v i))≤D:=mul_le_mul_of_nonneg_left (by unfold imageF; rw[hu,hv]; exact dist_le_pi_dist (imageF a p) (imageF a t) i) hq
          exact (dist_triangle _ (f u) _).trans ((add_le_add ih (hz.trans hm)).trans_eq (by rw [Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one]; ring))
    simpa only [Finset.card_univ,show X Finset.univ=t from by ext; simp [X]] using h Finset.univ
end Mesh
end YM.Fir
#print axioms YM.Fir.Mesh.snake
