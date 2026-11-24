import YM.QCD.Runnel.Cinch

/-! # spin-walk summation; canonical free operator has this precise stencil nature -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Rudder
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Bloch Metric
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
variable {n : Side} {I J : Type}
structure Gleam where
  w : Walk
  B : Spike
namespace Gleam
variable (G : Gleam)
def rate (δ : ℝ):=Real.exp (δ*G.w.length) * ‖G.B‖
def dept (t : Site n) (U : Grid n):=routeM t U G.w*onSpin n G.B
lemma valid (δ : ℝ): 0≤G.rate δ:=by unfold rate; positivity
lemma subdued {η δ : ℝ} (h : η≤δ): G.rate η≤G.rate δ:= by unfold rate; gcongr
lemma parity (t : Site n) (U : Grid n) (k : Frame n): G.dept t (gauge k U)= siteRot k*G.dept t U*star (siteRot k):=by
  unfold dept; rw [gaugeM]; simp only [mul_assoc]; rw [siteRot_star,(rot_spin ..).eq] -- check `rot_spin`
end Gleam
abbrev Ground := (n:Side) → Site n → Grid n → Sheet n
variable {P Q:Ground} {δ c C : ℝ} {G : I → Gleam} {D : J → Gleam}
structure Wages (δ c:ℝ) (G : I→ Gleam): Prop where
  po : 0≤δ
  val : Summable fun i=> (G i).rate δ
  cap : (∑' i,(G i).rate δ)≤ c
namespace Wages
variable (h : Wages δ c G)
include h
lemma chief : 0≤c := (tsum_nonneg (fun i=>(G i).valid δ)).trans h.cap
lemma reduces {ε p:ℝ} (he : 0≤ε) (hp : ε≤δ) (hc : c≤ p): Wages ε p G:= by
  have ht i:= (G i).subdued hp
  have hh:= h.val.of_nonneg_of_le (fun i=>(G i).valid ε) ht
  exact ⟨he,hh,(hh.tsum_le_tsum ht h.val).trans (h.cap.trans hc)⟩
lemma bp : Summable fun i=> ‖(G i).B‖:= by simpa only [Gleam.rate,zero_mul,Real.exp_zero,one_mul] using (h.reduces le_rfl h.po le_rfl).val
omit h in
lemma spinSize (n : Side) : ∃ C : ℝ,0 ≤ C ∧ ∀ i : Spike, ‖onSpin n i‖≤C*‖i‖:=by
  let L : Spike→L[ℂ] Sheet n := LinearMap.toContinuousLinearMap { toFun:=onSpin n,map_add':=fun _ _=> (on_spin_add ..).symm,map_smul':=fun i j=> by unfold onSpin wave; rw [Matrix.smul_kronecker,ride_smul]; rfl }
  exact ⟨‖L‖,norm_nonneg L,fun i=> L.le_opNorm i⟩
lemma applied (t : Site n)(U : Grid n): Summable fun i=> ‖(G i).dept t U‖:=by
  obtain ⟨C,hc,H⟩:=spinSize n; apply (h.bp.mul_left C).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro i; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (rotation_price (circle ..))).trans (H ..))
end Wages

def Shows (G : I → Gleam) (P : Ground) := ∀ n t U, HasSum (fun i=> (G i).dept t U) (P n t U)
def Feat (δ p : ℝ) (P : Ground) : Prop:= ∃ (I : Type) (G:I→ Gleam),Wages δ p G ∧ Shows G P
lemma Feat.mono (h : Feat δ c P) {u p : ℝ} (hp : 0≤u) (hu : u≤δ) (he : c≤p): Feat u p P := by obtain ⟨I,G,H,hG⟩:=h; exact ⟨I,G,H.reduces hp hu he,hG⟩
lemma Feat.plus (h : Feat δ c P) (e : Feat δ C Q): Feat δ (c+C) (P+Q):=by
  obtain ⟨I,G,H,hG⟩:=h; obtain ⟨J,K,L,hK⟩:=e
  let X : I⊕J → Gleam:=Sum.elim G K
  have hm : HasSum (fun i=>(X i).rate δ) ((∑' i,(G i).rate δ)+(∑' i,(K i).rate δ)):= HasSum.sum H.val.hasSum L.val.hasSum
  exact ⟨_,X,⟨H.po,hm.summable, hm.tsum_eq|>.trans_le (add_le_add H.cap L.cap)⟩,fun n t U=> HasSum.sum (hG n t U) (hK n t U)⟩
lemma paid_product {a:I→ℝ} {b:J→ℝ} (h : Summable a) (ha : ∀ i, 0≤a i) (g : Summable b) (hb : ∀ j, 0≤b j): Summable (fun i:I×J=> a i.1*b i.2):= by
  refine (summable_prod_of_nonneg (fun i=> mul_nonneg (ha i.1) (hb i.2))).mpr ⟨fun i=>g.mul_left (a i),?_⟩
  change Summable fun i:I=> ∑' j,a i*b j; simp_rw [tsum_mul_left]; exact h.mul_right _
def bump (G : I→Gleam) (K : J→ Gleam) : I×J → Gleam:= fun i=> ⟨(G i.1).w++(K i.2).w,(G i.1).B*(K i.2).B⟩
set_option maxHeartbeats 50000 in
lemma coinage (G I:Gleam)(δ : ℝ): Gleam.rate ⟨G.w++I.w,G.B*I.B⟩ δ ≤ G.rate δ * I.rate δ:=by
  unfold Gleam.rate; rw [List.length_append,Nat.cast_add,mul_add,Real.exp_add,mul_mul_mul_comm (Real.exp _) ‖G.B‖]; exact mul_le_mul_of_nonneg_left (norm_mul_le G.B I.B) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
lemma kicker (a:I→ℝ) (b:J→ℝ) (s:I×J→ℝ) (h1 : ∀ i,0≤a i) (h2 : ∀ i,0≤b i) (h3 : ∀ i,0≤s i)
    (h : ∀ i,s i≤a i.1*b i.2) (ha : Summable a) (hb : Summable b) (hx : ∑' i,a i≤c) (hy : ∑' i,b i≤C):
    Summable s ∧ ∑' i,s i≤c*C:=by
  let f (i:I×J):= a i.1*b i.2
  have hf := paid_product ha h1 hb h2
  have hh : Summable s:= Summable.of_nonneg_of_le h3 h hf
  have ht : ∑' i,s i≤(∑' i,a i)*(∑' i,b i):= (hh.tsum_le_tsum h hf).trans_eq (HasSum.mul ha.hasSum hb.hasSum hf).tsum_eq
  exact ⟨hh,ht.trans (mul_le_mul hx hy (tsum_nonneg h2) ((tsum_nonneg h1).trans hx))⟩
lemma bumped (H : Wages δ c G)(L: Wages δ C D): Wages δ (c*C) (bump G D):=by
  obtain ⟨a,b⟩:= kicker (fun i=>(G i).rate δ) (fun i=>(D i).rate δ) (fun i=>(bump G D i).rate δ) (fun i=> (G i).valid δ) (fun i=> (D i).valid δ) (fun i=>(bump G D i).valid δ)
    (fun i=> coinage (G i.1) (D i.2) δ) H.val L.val H.cap L.cap
  exact ⟨H.po,a,b⟩
lemma bump_eq (G:I→Gleam)(K:J→Gleam)(i) (n : Side)(t: Site n)(U:Grid n): (bump G K i).dept t U=(G i.1).dept t U*(K i.2).dept t U:=by
  unfold bump Gleam.dept; dsimp only; rw [appendM,← on_spin_mul]; simp only [mul_assoc]; rw [← mul_assoc (routeM t U (K i.2).w) (onSpin n (G i.1).B), (spinM t U (G i.1).B (K i.2).w).eq]; simp only [mul_assoc]
lemma Feat.prod (h : Feat δ c P) (e : Feat δ C Q): Feat δ (c*C) (P*Q):=by
  obtain ⟨I,G,H,hG⟩:=h; obtain ⟨J,K,L,hK⟩:=e
  have hz:= bumped H L
  refine ⟨_,_,hz,fun n t U=>?_⟩
  have hm: Summable (fun i:I×J=> (bump G K i).dept t U):=(hz.applied t U).of_norm
  have he:= (hG n t U).mul (hK n t U) (by simp_rw [bump_eq] at hm; exact hm)
  simp_rw [bump_eq]; exact he
lemma Feat.scale (h : Feat δ c P) (u : ℂ): Feat δ (‖u‖*c) (u • P):=by
  obtain ⟨I,G,H,hG⟩:=h; let X : I→ Gleam:= fun i=>⟨(G i).w,u • (G i).B⟩
  have he i:(X i).rate δ=‖u‖*(G i).rate δ:=by unfold Gleam.rate X; rw [norm_smul,mul_left_comm]
  refine ⟨_,X, ⟨H.po,?_,?_⟩,fun n t U=>?_⟩
  · simp_rw [he]; exact H.val.mul_left _
  · simp_rw [he,tsum_mul_left]; exact mul_le_mul_of_nonneg_left H.cap (by positivity)
  have he' i:(X i).dept t U=u • (G i).dept t U:=by simp only [X,Gleam.dept]; rw [← Matrix.mul_smul]; congr 1; simp only [onSpin,wave,Matrix.smul_kronecker,ride_smul]; rfl
  simp_rw [he']; exact (hG n t U).const_smul _
lemma Feat.neg (h : Feat δ c P) : Feat δ c (-P):= by simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using h.scale (-1)
lemma Feat.sub (h : Feat δ c P) (e : Feat δ C Q): Feat δ (c+C) (P-Q):=by simpa only [sub_eq_add_neg] using h.plus e.neg
lemma Feat.ad (h : Feat δ c P) : Feat δ c (star P):=by
  obtain ⟨I,G,H,hG⟩:=h; let X : I→ Gleam:= fun i=>⟨Lattice.reverse (G i).w,star (G i).B⟩
  have he i: (X i).rate δ= (G i).rate δ:=by simp [Gleam.rate,X,Lattice.reverse]
  refine ⟨_, X,⟨H.po,?_,?_⟩,fun n t U=>?_⟩
  · simp_rw [he]; exact H.val
  · simp_rw [he]; exact H.cap
  have hv i:(X i).dept t U=star ((G i).dept t U):=by unfold X Gleam.dept; rw [star_mul,on_spin_star, ← flipping]; exact (spinM ..).eq
  simp_rw [hv]; exact (hG n t U).star
lemma Feat.solo (h : 0 ≤δ) (X : Gleam): Feat δ (X.rate δ) (fun _ t U=>X.dept t U):=by
  refine ⟨Unit,fun _=>X, ⟨h,Summable.of_finite,?_⟩,fun n t U=>?_⟩
  · simp
  simpa using! hasSum_fintype (L:=SummationFilter.unconditional Unit) (fun _ : Unit=> X.dept t U) -- inspect args
lemma Feat.zero (h : 0≤δ) : Feat δ 0 0:= by
  have he:= Feat.solo h ⟨[],0⟩; simpa [Gleam.dept,Gleam.rate,on_spin_zero] using! he
lemma Feat.one (h : 0≤δ): Feat δ 1 1:= by
  have he:=Feat.solo h ⟨[],1⟩; simpa [Gleam.rate,Gleam.dept,routeM,on_spin_one, oneNorm] using! he
lemma Feat.group {U : I→Ground} {s:Finset I} {m:I→ℝ} (h : ∀ i∈s,Feat δ (m i) (U i)) (hp : 0≤δ): Feat δ (∑ i∈s, m i) (∑ i∈s,U i):=by
  classical
  induction s using Finset.induction_on with
  | empty=> simpa using Feat.zero hp
  | insert a s ha ih=> rw [sum_insert ha,sum_insert ha]; exact (h _ (mem_insert_self ..)).plus (ih (fun i hi=> h i (mem_insert_of_mem hi)))
end YM.QCD.Rudder
