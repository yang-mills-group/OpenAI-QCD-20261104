import YM.QCD.Flume.Reply

/-! # installation with signs. Reply rows from cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Flume
open Lat Para Lattice Wilson Function Finset Filter Set Matrix
open Laurent Bloch YM.Next.Free Metric Kit Free
open scoped Topology BigOperators Matrix Kronecker
variable {c f n : Side} {j k : ℕ} (P : Flight j k) (h : f.val=c.val*P.L.val)
local notation "r"=> sliceL P h

def occ (x : Site n) (u : Cover) := seamPath x (route 0 u 1)
lemma concord (p x : Site n) (u : Cover) : occ x u * scarf p (x+wrap n u) = scarf p x*mode (tuning p) u:= by unfold occ; have he:= follows p x (route 0 u 1); rw [wrap_stop, route_end] at he; exact he
lemma pathLength (x : Site n) (u : Cover) : ‖occ x u‖=1 := by
  have hx := congr_arg (fun v : ℂ=> ‖v‖) (realSeam x (route 0 u 1)).2
  rw [norm_mul,norm_one] at hx; unfold occ; nlinarith [norm_nonneg (seamPath x (route 0 u 1))]
lemma sign_rate (x : Site n) (u v : Cover) : occ x (u+v)=occ x u*occ (x+wrap n u) v:= by
  let p: Site n:=0
  let y:= x+wrap n u
  have he : x+wrap n (u+v)=y+wrap n v:= by rw [map_add,← add_assoc]
  apply mul_right_cancel₀ (scarf_ne p (x+wrap n (u+v)))
  rw [concord,he,mul_assoc,concord,mode_shift,← mul_assoc,← concord p x u,mul_assoc]
lemma principal (p x : Site c) (l i : Site P.L) :
    scarf (twins r p i) ((sliceL P h).assemble (x,l))=occ ((sliceL P h).embed x) (lift l)*((P.L.val:ℂ)⁻¹^2)*scarf p x* mode (aliasAt (tuning p) i) (lift l):=by
  have he:= concord (twins r p i) ((sliceL P h).embed x) (lift l); rw [full_tune r P.odd,welcome r P.odd] at he
  have hh := congr_arg (occ ((sliceL P h).embed x) (lift l) *·) he; simp only [← mul_assoc] at hh
  rw [show occ ((sliceL P h).embed x) (lift l) * occ _ _ = 1 from (realSeam ..).2,one_mul] at hh; exact hh

/-- continuous real tapes put together -/
def fonts (P : Flight j k) (u : List Axis) (i : Site P.L) (a b : Fiber) (x : Cover) :=
  (slope P.L:ℂ)*((meshBook (yip false) 1 u P (i,a) b x:ℂ)+Complex.I*(meshBook (yip true) 1 u P (i,a) b x:ℂ))
lemma budgeted_add {x y : Cover→ℂ} {σ a b : ℝ} (hx : Width σ a x) (hy : Width σ b y) : Width σ (a+b) fun z=>x z+y z := by
  unfold Width at *
  have he (z : Cover): Real.exp (σ * size z)*‖x z+y z‖ ≤ Real.exp (σ*size z)*‖x z‖+Real.exp (σ*size z)*‖y z‖ := by rw [← mul_add]; gcongr; exact norm_add_le _ _
  have hn (z : Cover) : 0 ≤ Real.exp (σ * size z)*‖x z+y z‖ := by positivity
  have hs:=hx.2.1.add hy.2.1
  have hu:=hs.of_nonneg_of_le hn he
  refine ⟨hn,hu,(hu.tsum_le_tsum he hs).trans ?_⟩
  rw [Summable.tsum_add hx.2.1 hy.2.1]; exact add_le_add hx.2.2 hy.2.2
lemma budgeted_coin {x : Cover→ℂ} {σ a : ℝ} (hx : Width σ a x) (r' : ℂ) : Width σ (‖r'‖*a) fun z=> r'*x z:=by
  have he (z : Cover) :Real.exp (σ*size z)*‖r'*x z‖=‖r'‖*(Real.exp (σ*size z)*‖x z‖):=by rw [norm_mul]; ring
  simp only [Width,he,RG.SumBudget]; refine ⟨fun _=> by positivity,hx.2.1.mul_left _,?_⟩; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hx.2.2 (norm_nonneg _)
lemma budgeted_real {x : Cover→ℝ} {σ a : ℝ} (hx : Width σ a x):Width σ a fun i=> (x i:ℂ) := by simpa only [Width,Complex.norm_real] using! hx

lemma reserves_font (hj : 4≤j) (hk : 4≤k) : ∃ σ C : ℝ, 0<σ ∧ 0<C ∧ ∀ (P : Flight j k) i (u : List Axis), u.length≤j-2→ ∀ a b,
    Width σ (C*slope P.L/(P.L.val:ℝ)^(1+u.length)) (fonts P u i a b):=by
  obtain ⟨σ,C,hp,hc,H⟩:= (supplied true hj hk).honored hj 1
  obtain ⟨η,D,he,hd,h⟩:= (supplied false hj hk).honored hj 1
  have ht := lt_min hp he
  refine ⟨min σ η,C+D,ht,by linarith,fun P i u hx a b=>?_⟩
  have hs:= H P u hx; have hg:=h P u hx
  rw [(supplied true hj hk).traverse hj 1 hx] at hs; rw [(supplied false hj hk).traverse hj 1 hx] at hg
  have hi:= (budgeted_coin (budgeted_add (budgeted_real ((hg (i,a) b).mono (min_le_right σ η) le_rfl)) (budgeted_coin (budgeted_real ((hs (i,a) b).mono (min_le_left σ η) le_rfl)) Complex.I)) (slope P.L:ℂ))
  exact hi.mono le_rfl (le_of_eq (by simp only [Complex.norm_I,Complex.norm_real,Real.norm_of_nonneg (slope_pos _).le]; ring))
lemma per_f (hj : 4≤j) (hk : 4≤k) (u : List Axis) (hu : u.length≤j-2) (p) (hp : p∈baseCube) (i : Site P.L) a b :
    Laurent.read (fonts P u i a b) p = (slope P.L:ℂ)* spread (shout false) 1 u P i p a b:= by
  let U (c : Bool) := meshBook (yip c) 1 u P
  have ht (c : Bool) : Summable (fun x=> ‖U c (i,a) b x‖) := (supplied c hj hk).bankSafe hj 1 hu P _ _
  let f (c : Bool) (x : Cover):= mode p x*(U c (i,a) b x:ℂ)
  have hh c: Summable (f c):=by unfold f; exact Summable.of_norm (by simpa only [norm_mul, Complex.norm_real, mode_real _ _ hp.1,one_mul] using ht c)
  have he c: ∑' x,f c x= spread (yip c) 1 u P i p a b:= (supplied c hj hk).bankRead hj 1 hu P _ hp _ _
  have hw x : mode p x*fonts P u i a b x=(slope P.L:ℂ)*(f false x+Complex.I*f true x):=by unfold fonts f U; ring
  unfold Laurent.read; simp_rw [smul_eq_mul,hw,tsum_mul_left]; rw [Summable.tsum_add (hh false) ((hh true).mul_left _),tsum_mul_left,he,he]
  congr 1; unfold spread; simp only [Matrix.sum_apply]; rw [Finset.mul_sum,← sum_add_distrib]; apply sum_congr rfl; intro l _; rw [reunited P p l]; simp only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul]; ring

lemma boots (x p : Site c) (a b : Fiber) (i : Site P.L) (hj : 4≤j) (hk : 4≤k) (u : List Axis) (hu : u.length≤j-2) :
    (oldDiff (proton P h) u*leaf c) ((sliceL P h).assemble (x,i),a) (p,b)=occ ((sliceL P h).embed x) (lift i)*scarf p x*Laurent.read (fonts P u i a b) (tuning p) := by
  rw [per_f P hj hk u hu _ (keyboard _),trailbill, spread, Matrix.sum_apply,Finset.mul_sum,Finset.mul_sum]; apply sum_congr rfl; intro l _; rw [principal P h]; simp only [gain,Matrix.smul_apply,YM.Next.Free.toll,pow_one]; rw [full_tune r P.odd]; simp only [smul_eq_mul]; field_simp [side_ne P.L]

-- actual periodization with signs
variable {A B : Type*}
def splashL (x : Site n) (X : Cover→ℂ) (y : Site n) (u : Cover):ℂ:= if x+wrap n u=y then occ x u * X u else 0
def sprayL (x : Site n) (X : Cover→ℂ) (y : Site n):ℂ:= ∑' u : Cover,splashL x X y u
lemma splash_budget (x y : Site n) {X : Cover→ℂ} (hs : Summable fun u=>‖X u‖): Summable fun u=>‖splashL x X y u‖:= by apply hs.of_nonneg_of_le (fun _=>norm_nonneg _); intro z; unfold splashL; split <;> simp [pathLength]
lemma spray_read (x p : Site n) {X : Cover→ℂ} (hs : Summable fun u=>‖X u‖) :
    ∑ y, sprayL x X y * scarf p y=scarf p x * Laurent.read X (tuning p):=by
  unfold sprayL Laurent.read; simp_rw [← tsum_mul_right]; rw [← Summable.tsum_finsetSum (f:=fun (i : Site n) u=> splashL x X i u * scarf p i) (fun i _=> ((splash_budget x i hs).of_norm.mul_right _)), ← tsum_mul_left]
  apply tsum_congr; intro z; rw [sum_eq_single (x+wrap n z)]
  · rw [splashL,if_pos rfl, mul_right_comm,concord]; ring
  · intro i _ hi; simp [splashL,Ne.symm hi]
  simp

def printed (u : List Axis): Matrix (Lat.Row f) (Lat.Row c) ℂ := of fun i y=>
    let p : Site c := (sliceL P h).parent i.1
    let l : Site P.L := (sliceL P h).residue i.1
    occ ((sliceL P h).embed p) (lift l)*sprayL p (fonts P u l i.2 y.2) y.1
lemma prints (u : List Axis) (x y : Site c) (i : Site P.L) (a b : Fiber) : printed P h u ((sliceL P h).assemble (x,i),a) (y,b)=occ ((sliceL P h).embed x) (lift i)*sprayL x (fonts P u i a b) y := by simp [printed]
lemma eligible (hj : 4≤j) (hk : 4≤k) (u : List Axis) (hu : u.length≤j-2): oldDiff (proton P h) u=printed P h u:=by
  have he : oldDiff (proton P h) u*leaf c=printed P h u*leaf c:=by
    ext ⟨p,a⟩ ⟨y,b⟩
    obtain ⟨⟨x,l⟩,rfl⟩:=(sliceL P h).assemble_bijective.2 p
    rw [boots P h x y a b l hj hk u hu,Matrix.mul_apply,Fintype.sum_prod_type]; symm
    obtain ⟨σ,C,hσ,hc,H⟩:=reserves_font hj hk
    have hm : Summable fun v=> ‖fonts P u l a b v‖ := ((H _ _ _ hu a b).unweighted hσ.le).2.1
    simp only [bare_leaf,Matrix.one_apply,mul_ite,mul_one,mul_zero,sum_ite_eq',Finset.mem_univ,↓reduceIte]; simp_rw [prints]; rw [mul_assoc]; rw [← spray_read x y hm,Finset.mul_sum]; apply sum_congr rfl; intro i _; ring
  have hg := congr_arg (fun X : Matrix (Lat.Row f) (Lat.Row c) ℂ=> X*star (leaf c)) he; simpa only [Matrix.mul_assoc,(leaf_u c).2, Matrix.mul_one] using hg
end YM.QCD.Flume
