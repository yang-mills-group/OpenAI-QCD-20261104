import YM.QCD.Flume.Laurel
-- no Pulled import; rederive equiv

/-! # Recipe with actual stencil exception for top, at arbitrary homogeneous gauges -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set
open Laurent Bloch YM.Next.Free Metric
open scoped Topology BigOperators
variable {ι : Type*} {j : ℕ}
lemma flash_reread (s : Signed) (p : Momentum) (u : Cover→ℝ) : RRead u (s.act p)= RRead (fun i=> u (s.act i)) p:=by
  unfold RRead Laurent.read; rw [← (Signed.actEquiv (R:=ℤ) s).toEquiv.tsum_eq]; refine tsum_congr fun i=>?_; change mode (s.act p) (s.act i) • _= _
  have hh : mode (s.act p) (s.act i)=mode p i:=by
    unfold mode; rw [← Equiv.sum_comp s.perm (fun j => s.act p j*(↑(s.act i j):ℂ))];
    congr! 2; apply Finset.sum_congr rfl; intro a _; rw [Signed.act_at,Signed.act_at]; split <;> simp
  rw [hh]; rfl

structure Plan (j : ℕ) where
 δ : ℝ
 μ : ℝ
 good : 2≤j
 funds : 0<δ
 price : 0<μ
 below : μ<1/2
 ballad : ∀ v : Train j, ∀ p∈realCube zone, ∀ a, 2*μ ≤ (ranked v δ p a).re
lemma passport (h : 2≤j): Nonempty (Plan j):=by
  obtain ⟨δ,b,hδ,hb,H⟩:= new_law h
  let μ:= min (b/2) (1/3)
  refine ⟨⟨δ,μ,h,hδ,lt_min (by positivity) (by norm_num),lt_of_le_of_lt (min_le_right ..) (by norm_num),fun v p hp a=>le_trans ?_ (ranking H p hp v a)⟩⟩; have he : μ ≤ b/2:=min_le_left ..; linarith
namespace Plan
variable (P : Plan j)
def knot (v : Train j) (a : Axis) (p : Momentum) := Complex.sqrt (ranked v P.δ p a - (P.μ:ℂ))
lemma spark_k (v : ι → Train j) (a : ι→Axis): Moderate (fun _:ι=>1) fun i=> P.knot (v i) (a i):= by
  refine radiant ((rated P.good v P.funds _).sub (Moderate.const _)) zone_pos P.price ?_
  intro i p hp; have ht:=P.ballad (v i) p hp (a i); change _ ≤ (_-(P.μ:ℂ)).re; rw [Complex.sub_re, Complex.ofReal_re]; exact le_sub_iff_add_le.mpr (by rwa [← two_mul])
lemma root_knots (v : Train j) (a) (p) (hp : p ∈ realCube zone) :
    star (P.knot v a (-p))= P.knot v a p ∧ (P.knot v a p)^2=ranked v P.δ p a - (P.μ:ℂ) ∧ star (P.knot v a p)=P.knot v a p := by
  have he:= symmetry P.good P.δ p v a hp
  let x := ranked v P.δ p a - (P.μ:ℂ)
  have hx : star x=x:=by simp only [x,star_sub,he.1,Complex.star_def,Complex.conj_ofReal]
  have hs : 0<x.re:= by unfold x; rw [Complex.sub_re,Complex.ofReal_re]; linarith [P.ballad v p hp a,P.price]
  have hh : x ≠ 0:= norm_pos_iff.mp (hs.trans_le (Complex.re_le_norm _))
  have hT : star (Complex.sqrt x)=Complex.sqrt x:=by
    rw [Complex.sqrt_eq_real_add_ite]; have ht:((x.re:ℂ))=x:=Complex.ext rfl (Eq.symm (Complex.conj_eq_iff_im.mp hx)); have hu : ‖x‖=x.re:=by rw [← ht]; simp [Real.norm_of_nonneg hs.le]
    simp [hu]
  unfold knot; rw [he.2]; exact ⟨hT,pow_two x.sqrt|>.trans (cmag hh),hT⟩
lemma over (v : Train j) (a) : Overlaps zone (P.knot v a):= fun p hp x hx=> congr_arg Complex.sqrt (congr_arg (fun z=> z - (P.μ:ℂ)) (rang v P.δ _ p hp _ hx))

def version (v : Train j) (a : Axis) := tape (P.knot v a)
lemma readsK (v : Train j) (p) (hp : p∈baseCube) (a): RRead (P.version v a) p=P.knot v a p:=by
  obtain ⟨η,hc,h⟩:=tapes_read (spark_k P (fun _:Unit=>v) (fun _=>a)) zone_pos (fun _=>P.over v a) (fun i p hp=> (root_knots P v a p hp).1)
  exact h () p (base_subset_realCube hc hp)
lemma tapeQ (v : ι→Train j) (a : ι→ Axis): SoundTape (fun _ : ι=>1) fun i=> P.version (v i) (a i):= tapes_sound (spark_k P v a) zone_pos fun i=> P.over (v i) (a i)
lemma version_step (s : Signed) (v : Train j) (a : Axis) (x : Cover) : P.version v (s.perm a) (s.act x)=P.version v a x:=by
  obtain ⟨σ,C,hp,hc,H⟩:=P.tapeQ (fun i:Axis=>v) id
  have ht:= (Signed.actEquiv (R:=ℤ) s).toEquiv.summable_iff.mpr ((H (s.perm a)).unweighted hp.le).2.1
  let f x := P.version v (s.perm a) (s.act x)
  have hh : f=P.version v a := by
    apply RRead_injective ht ((H a).unweighted hp.le).2.1; intro p he; rw [readsK P _ _ he]; change RRead f p=P.knot v a p; unfold f; rw [← flash_reread s p, readsK P _ _ (bank_acts _ he s),knot, ranks]; rfl
  exact congr_fun hh x

/-- stencil choice for explicit top; top can't pass same positive extension. -/
def flatPeak (v : Train j) : Prop := v=Train.top j
def clove : Cover→ℝ := fun x=> Real.sqrt (1/2-P.μ) * token 0 x
def Herm (v : Train j) (a) (x : Cover) := by classical exact if flatPeak v then P.clove x else P.version v a x
lemma herm_sym (v : Train j) (a) (s : Signed) (x) : P.Herm v (s.perm a) (s.act x)=P.Herm v a x:=by
  unfold Herm; split_ifs
  · have hh : s.act x=0 ↔ x=0:=by nth_rw 1 [← show s.act (0:Cover)=0 by simp]; exact s.act_injective.eq_iff
    simp [clove,token,hh]
  exact P.version_step ..
lemma herm_paid (v : ι →Train j) (a : ι→Axis): SoundTape (fun _ : ι=>1) fun i=> P.Herm (v i) (a i):=by
  obtain ⟨σ,C,hp,hc,H⟩:= P.tapeQ v a
  have he := YM.Next.Free.Width.scale_line (Real.sqrt (1/2-P.μ)) (token_rate 0 σ)
  refine ⟨σ, max C (‖Real.sqrt (1/2-P.μ)‖*envelopeW σ 0),hp,lt_max_of_lt_left hc,fun i=>?_⟩
  by_cases hi : flatPeak (v i)
  · dsimp only; rw [show P.Herm (v i) (a i)=P.clove by funext; simp [Herm,hi]]; rw [mul_one]; exact he.mono le_rfl (le_max_right ..)
  dsimp only; rw [show P.Herm (v i) (a i)=P.version (v i) (a i) by funext; simp [Herm,hi]]; exact (H i).mono le_rfl (by rw [mul_one,mul_one]; exact le_max_left ..)
lemma peak_read (p) : RRead P.clove p=(Real.sqrt (1/2-P.μ):ℂ):=by
  unfold RRead clove Laurent.read
  simp only [Complex.ofReal_mul,smul_eq_mul]; rw [tsum_eq_single 0]
  · simp [token]
  intro x hx; simp [token,hx]
lemma clovely (v : Train j) p (hp : p ∈ baseCube) a : star (RRead (P.Herm v a) p)=RRead (P.Herm v a) p:= by
  by_cases hi : flatPeak v
  · have hh : P.Herm v a=P.clove:=by funext x; simp [Herm,hi]
    rw [hh,P.peak_read]; simp -- format
  have hh : P.Herm v a=P.version v a:=by funext x; simp [Herm,hi]
  rw [hh,P.readsK v _ hp]; exact (P.root_knots v a p (base_subset_realCube zone_pos hp)).2.2

lemma certified (v : Train j) (p : Momentum) (hp : p∈baseCube): hemi v p=∑ i, plusD p i*((P.μ:ℂ)+ RRead (P.Herm v i) p ^2) := by
  by_cases hi : flatPeak v
  · have hh i : P.Herm v i=P.clove:=by funext x; simp [Herm,hi]
    unfold flatPeak at hi
    simp_rw [hh,peak_read,← Complex.ofReal_pow, Real.sq_sqrt (sub_nonneg.mpr P.below.le)]
    rw [hi,hemi,Dir_top, ← Finset.sum_mul, toward,← chip_gap]; push_cast; ring
  have hh i : P.Herm v i=P.version v i:=by funext x; simp [Herm,hi]
  simp_rw [hh,readsK P _ _ hp,fun a=>(P.root_knots v a p (base_subset_realCube zone_pos hp)).2.1,add_sub_cancel]
  rw [rank_law P.good v P.δ P.funds p hp]
end Plan
end YM.QCD.Flume
