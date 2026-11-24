import YM.QCD.Quarry.Gems

/-! # Natural matrix families on odd replicas -/
set_option autoImplicit false
noncomputable section
open YM.Next.Free
namespace YM.QCD.Quarry
open Function Lattice Wilson Lat Flume Kit Revolve Free Finset Filter Laurent Rudder
open YM.Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators
variable {n N m f F : Side} {M k j : ℕ}
def stream (G : Window n N M) (d : Site N→ℂ) : Rail N n:= Matrix.of fun i j=>if (G.cut i.1,i.2)=j then d i.1 else 0
lemma streams (G : Window n N M) (d : Site N→ℂ) {X : Type*} (B : Matrix (Row n) X ℂ) (i: Site N)(a : Fiber)(j:X):
    (stream G d*B) (i,a) j=d i* B (G.cut i,a) j:=by
  rw [Matrix.mul_apply,sum_eq_single (G.cut i,a)]; · simp [stream]
  · intro k _ hk; simp [stream,Ne.symm hk]
  simp
lemma peered (G : Window n N M) (d : Site N→ℂ) (σ : Equiv.Perm (Site N)) (P : Site N→Bundle)
    (τ : Equiv.Perm (Site n)) (X : Site n→Bundle) (h : ∀ x,G.cut (σ x)=τ (G.cut x)) (he : ∀ x, d (σ x) • P x=d x • X (G.cut x)) :
    rides σ P * stream G d=stream G d* rides τ X:=by
  ext ⟨x,a⟩ ⟨y,b⟩; rw [streams,Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single (σ x)]
  · by_cases hi : τ (G.cut x)=y
    · simp [rides,stream,h,hi]; have hh:= congr_arg (fun L:Bundle=> L a b) (he x); simpa [mul_comm] using hh -- simp?
    simp [rides,stream,h,hi]
  · intro i hi hh; simp [rides,Ne.symm hh]
  simp
variable {G : Window n N M} {d : Site N→ℂ} (hd : Quaint G d)
include hd
lemma rays_across (a : Step) (U : Grid n) : leg 0 (G.links U) a* stream G d=stream G d * leg 0 U a:=by
  rw [leg_day,leg_day]; apply peered G d _ _ _ _ (fun x=> G.uniform x a); intro x
  unfold touch hitch; simp only [Matrix.kronecker_smul,smul_smul,G.read]; rw [mul_comm (d _), show (Equiv.addRight a.vec x)=(x+a.vec) from rfl, hd.lift]
lemma ray_paths (U : Grid n) (w : Walk): routeM 0 (G.links U) w * stream G d= stream G d * routeM 0 U w:=by
  induction w with
  | nil=> simp [routeM]
  | cons a w ih=>change (leg _ _ _ * routeM _ _ _)*stream G d=_*(leg _ _ _*routeM _ _ _); rw [Matrix.mul_assoc,ih,← Matrix.mul_assoc,rays_across hd,Matrix.mul_assoc]
lemma pint (U : Grid n) (B:Bloom k): B.tonic 0 (G.links U)*stream G d=stream G d* B.tonic 0 U:=by
  unfold Bloom.tonic; rw [Matrix.mul_assoc,ray_paths hd,← Matrix.mul_assoc]; rw [← Matrix.mul_assoc]; congr 1
  refine peered G d _ _ _ _ (fun x=> rfl) fun x=>?_ ; unfold Bloom.taste RG.Slot.atSite; rw [G.expansion]; rfl
lemma grade_odd (U : Grid n) (B:Gleam) : B.dept 0 (G.links U)*stream G d=stream G d* B.dept 0 U:=by
  unfold Gleam.dept; rw [Matrix.mul_assoc,show onSpin N B.B*stream G d=stream G d * onSpin n B.B from peered _ _ _ _ _ _ (fun x=>rfl) (fun x=>rfl),← Matrix.mul_assoc, ray_paths hd,Matrix.mul_assoc]
lemma pours (x : Site N) (w : Walk) : shimmer 0 x w*d (stop x w)=d x * shimmer 0 (G.cut x) w:=by
  induction w generalizing x with
  | nil=> simp [shimmer,stop]
  | cons a w ih=> rw [shimmer,shimmer,stop,mul_assoc,ih,G.uniform, ← mul_assoc, hd.lift, mul_assoc]
omit hd
variable {c C : Side} (B : Flight j k) {h : f.val=c.val*B.L.val} {H : F.val=C.val*B.L.val}
  (G : Lace (P:=B.patch) h H M) {p : Site F→ℂ} (hp : Quaint G.high p)
include hp
lemma descend : Quaint G.low (p ∘ G.R.embed):=by
  refine ⟨fun x=> hp.sign _, fun i a=>?_⟩
  have hx:=pours hp (G.R.embed i) (List.replicate B.L.val a);
  rw [G.stake,show (0:Site F)=G.R.embed 0 from (G.R.root.map_zero).symm,show (0:Site f)=G.r.embed 0 from G.r.root.map_zero.symm] at hx -- maybe rewrite all 0 causing lower index
  erw [chord G.R i 0, cone G.R, chord G.r] at hx; exact hx
lemma valve : scoop G.R*stream G.high p=stream G.low (p∘G.R.embed)*scoop G.r := by
  ext ⟨x,a⟩ j; rw [streams,shows]; unfold stream scoop; simp only [mouth, Matrix.of_apply, Function.comp_apply,G.stake]; split <;> simp
lemma bolt : (scoop G.R)ᴴ*stream G.low (p∘G.R.embed)=stream G.high p*(scoop G.r)ᴴ:=by
  ext ⟨x,a⟩ ⟨y,b⟩; rw [streams]
  obtain ⟨⟨x,i⟩,rfl⟩:= G.R.assemble_bijective.2 x
  
  have h₁ (w : Site C)(j) : G.R.embed w=G.R.assemble (x,j)↔ w=x ∧ j=0:=by
    have H : G.R.embed w=G.R.assemble (w,0):=by simp [Ratio.assemble,lift] -- inspect
    rw [H,G.R.assemble_bijective.1.eq_iff,Prod.mk.injEq, eq_comm (a:=0)]
  have h₂ (w : Site c)(j) : G.r.embed w= G.high.cut (G.R.assemble (x,j)) ↔ w=G.low.cut x ∧ j=0:=by
    have H : G.r.embed w=G.r.assemble (w,0):=by simp [Ratio.assemble,lift]
    rw [H,G.regions,G.r.assemble_bijective.1.eq_iff,Prod.mk.injEq,eq_comm (a:=0)]
  by_cases he:i=0
  · subst i
    have H:= (h₁ x 0).mpr ⟨rfl,rfl⟩
    rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single x]
    · by_cases hh:y=G.low.cut x <;> simp [scoop,mouth,stream,h₁,h₂,hh,H, Ne.symm, eq_comm (a:=b) (b:=a)] -- H may loop
    · intro j _ hj; simp [scoop,mouth,h₁,hj]
    simp
  rw [Matrix.mul_apply,Fintype.sum_prod_type]; simp [scoop,mouth,h₁,h₂,he]
lemma fits_coins (U : Grid f):
    tied B H 0 (G.high.links U)*stream G.high p=stream G.low (p∘G.R.embed)*tied B h 0 U∧
    (tied B H 0 (G.high.links U))ᴴ*stream G.low (p∘G.R.embed)=stream G.high p*(tied B h 0 U)ᴴ:=by
  constructor
  · unfold tied lineF; simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.sum_mul,Matrix.mul_sum]
    have he (x : Cover)(i:Lattice.Order): (scoop (sliceL B H) * routeM 0 (G.high.links U) (route 0 x i))* stream G.high p=stream G.low (p∘G.R.embed)*(scoop (sliceL B h)*routeM 0 U (route 0 x i)):=by rw [Matrix.mul_assoc,ray_paths hp,← Matrix.mul_assoc]; erw [valve B G hp, Matrix.mul_assoc]; rfl
    simp_rw [he]
  unfold tied lineF; simp only [Matrix.mul_smul, Matrix.smul_mul,Matrix.conjTranspose_sum, Matrix.mul_sum, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, Matrix.sum_mul]
  have he (w : Walk): ((routeM 0 (G.high.links U) w)ᴴ*(scoop (sliceL B H))ᴴ)*stream G.low (p∘G.R.embed)=stream G.high p*((routeM 0 U w)ᴴ*(scoop (sliceL B h))ᴴ):=by rw [Matrix.mul_assoc]; erw [bolt B G hp,← Matrix.mul_assoc,← Matrix.star_eq_conjTranspose,← flipping,ray_paths hp, flipping,Matrix.star_eq_conjTranspose,Matrix.mul_assoc]; rfl
  simp_rw [he]
end YM.QCD.Quarry
