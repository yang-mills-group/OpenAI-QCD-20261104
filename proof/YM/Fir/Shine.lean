import YM.Fir.Willow
/-! Discrete Arzela and recovery of all forward-difference slots without interchange of derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.Fir.Mesh
open NoteF Set Function Filter Metric
open scoped Topology
variable {I X: Type*}[Fintype I] [DecidableEq I] [MetricSpace X] {f:ℕ→(I→ℤ)→ X}{U:Set (I→ℝ)}
variable {a:ℕ→ℝ}(ha:∀ i,0<a i)(hT:Tendsto a atTop (𝓝 0)) {x y:I→ℝ}
include ha hT
lemma watching {x:I→ℝ}: (noteF (fun i=>imageF (a i)) x).NeBot:=fullness (visible x ha hT) -- I arg nonexistent
lemma track {g:X}(h:seesF (fun i=>imageF (a i)) f x g): Tendsto (fun i=> f i (markF (a i) x)) atTop (𝓝 g):=h.comp (ride (fun i=>i) (fun i=>_) tendsto_id (visible x ha hT))
omit ha hT
abbrev quiet (a:ℕ→ℝ)(f:ℕ→(I→ℤ)→X) (x:I→ℝ):Prop:=∃ r C:ℝ,0<r∧ 0 ≤ C∧ ∀ᶠ i in atTop,∀ p,imageF (a i) p∈ball x r→∀ y,imageF (a i) y∈ball x r→ dist (f i p) (f i y) ≤ C * dist (imageF (a i) p) (imageF (a i) y)
abbrev damp (a:ℕ→ℝ)(f:ℕ→(I→ℤ)→X)(x:I→ℝ):Prop:=∃ r C:ℝ,0 < r∧0 ≤ C ∧∀ᶠ i in atTop,∀ p,imageF (a i) p∈ball x r→∀ b:I, dist (f i (advanceF b p)) (f i p)≤ C*a i
namespace Quiet
include ha
lemma from_damp (h:damp a f x): quiet a f x:=by
    obtain ⟨r,C,hr,hC,h⟩:=h; refine ⟨r, (Fintype.card I)*C,hr,mul_nonneg (by positivity) hC,h.mono (fun i hi p hp q hq=>?_ )⟩
    exact (snake _ hr (ha i) hC (fun p hx b _=> hi p hx b) p q hp hq).trans_eq (mul_assoc ..).symm
include hT
lemma awoken (h:quiet a f x) (g:X) (H:Tendsto (fun i=> f i (markF (a i) x)) atTop (𝓝 g)): seesF (fun i=>imageF (a i)) f x g:=by
    obtain ⟨r,C,h,q,hh⟩:=h
    let k :ℕ→ (I→ℤ):= fun i=> markF (a i) x
    let Y (i:ℕ)(p:I→ℤ):= imageF (a i) p; let F:=noteF Y x
    have ht:Tendsto (fun p:ℕ×(I→ℤ)=>Y p.1 (k p.1)) F (𝓝 x):= (visible x ha hT).comp beyond
    have hm:Tendsto (fun p:ℕ×(I→ℤ)=> C*dist (Y p.1 p.2) (Y p.1 (k p.1))+dist (f p.1 (k p.1)) g) F (𝓝 0):=by
        have hu:= ((approach.dist ht).const_mul C).add ((H.comp (beyond (v:=Y) (x:=x))).dist (tendsto_const_nhds (x:=g))); simpa only [Function.comp_def,dist_self,mul_zero,zero_add] using hu
    apply Metric.tendsto_nhds.mpr; intro ε he
    have hx :∀ᶠ i in F, Y i.1 i.2∈ball x r:= approach.eventually (ball_mem_nhds _ h)
    filter_upwards [hm.eventually_lt_const he,beyond.eventually hh,hx,ht.eventually (ball_mem_nhds _ h)] with p hp h hi hz; exact lt_of_le_of_lt ((dist_triangle _ (f p.1 (k p.1)) g).trans (add_le_add (h _ hi _ hz) le_rfl)) hp
variable [CompleteSpace X]
lemma dense {R:Set U}(x:U)(h:quiet a f x.val) (he:Dense R)(ht:∀ v ∈ R,CauchySeq (fun i=> f i (markF (a i) (v:U).val))): ∃ m:X,seesF (fun i=>imageF (a i)) f x.val m:=by
    suffices h' : CauchySeq (fun i=> f i (markF (a i) x.val)) by obtain ⟨g,H⟩:= cauchySeq_tendsto_of_complete h'; exact ⟨_,awoken ha hT h g H⟩
    obtain ⟨r,C,hr,hC,h⟩:= h; apply Metric.cauchySeq_iff.mpr; intro ε he'
    have ε':0<ε/4:=by positivity
    let O:= {u:U | u.val∈ball x.val r ∧ C*dist (x:U).val u.val<ε/4}
    have hU: IsOpen O:= (isOpen_ball.preimage continuous_subtype_val).inter (isOpen_lt (Continuous.const_mul (continuous_const.dist continuous_subtype_val) _) continuous_const)
    obtain ⟨v,hx,⟨hv,hL⟩⟩:=he.exists_mem_open hU ⟨x,Metric.mem_ball_self hr,by simpa using ε'⟩
    let F(v:U)(i:ℕ):= f i (markF (a i) v.val); have H':∀ᶠ i in atTop, dist (F x i) (F v i)< ε/4:=by
        have ht:= visible v.val ha hT; have hg:= visible x.val ha hT; filter_upwards [h, ht.eventually (isOpen_ball.mem_nhds hv),hg.eventually (ball_mem_nhds _ hr), ((hg.dist ht).const_mul C).eventually_lt_const hL] with i hi hu he h'; exact lt_of_le_of_lt (hi _ he _ hu) h'
    obtain ⟨N,hN⟩:= (Metric.cauchySeq_iff.mp (ht v hx) _ ε'); obtain ⟨M,hM⟩:= eventually_atTop.mp H'; refine ⟨max N M, fun i hi j hj=>?_⟩; have ha:= hN i ((le_max_left ..).trans hi) j ((le_max_left ..).trans hj); have hu:= hM i ((le_max_right ..).trans hi); have hz:= hM j ((le_max_right ..).trans hj); change dist (F v i) (F v j)<_ at ha; change dist (F x i) (F x j)<_; linarith only [hu,hz,ha,dist_triangle_right (F x i) (F x j) (F v j),dist_triangle (F x i) (F v i) (F v j),ε']
end Quiet
-- Recover linear estimate.Point is ALL orientations. local real derivative
end YM.Fir.Mesh
#print axioms YM.Fir.Mesh.Quiet.dense
