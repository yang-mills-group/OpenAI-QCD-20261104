import YM.Bloom.Span
/-! # low budgets actual curtains pricing cumulative. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bloom
open Function Lattice Laurent Bloch Metric RG Filter Arise
open Finset YM.Bank Precision Matrix Exterior Learn AnalyticBridge.LocalGaussianLaws.Current
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator
variable {H K F W:Type*}{j k n m l ℓ r:ℕ}
variable {c f:Side}{a b:ℝ}
local notation "θ"=> TypeFace 2
local notation "δ"=> TypeFace 1
noncomputable def billP (f:Side)(J:Matrix (Co f θ) H ℝ)(x:Cover)(i:θ)(v:H) : Parc→ₗ[ℝ]ℝ where
   toFun w:=(stalk f x i w*J) () v
   map_add' a b:= by rw[map_add,Matrix.add_mul,Matrix.add_apply]; -- rfl?
   map_smul' a x:=by rw [map_smul,Matrix.smul_mul, Matrix.smul_apply]; rfl
-- for arbitrary scaled low
noncomputable def pairP (f:Side)(J:Matrix (Co f θ) (Co f θ) ℝ) (x y:Cover)(i j:θ)(P Q:Parc):ℝ := (stalk f x i P*J*(stalk f y j Q).transpose) () ()
noncomputable def wishedL (f:Side)(J:Matrix (Co f θ) (Co f θ) ℝ) (x y:Cover)(i j:θ)(Q:Parc): Parc→ₗ[ℝ]ℝ where
    toFun P:=pairP f J x y i j P Q
    map_add' a b:=by unfold pairP; rw [map_add,Matrix.add_mul,Matrix.add_mul, Matrix.add_apply]
    map_smul' r a:=by unfold pairP; rw [map_smul,Matrix.smul_mul,Matrix.smul_mul,Matrix.smul_apply]; rfl
noncomputable def wishedR (f:Side)(J:Matrix (Co f θ) (Co f θ) ℝ) (x y:Cover)(i j:θ)(Q:Parc): Parc→ₗ[ℝ]ℝ where
    toFun P:=pairP f J x y i j Q P
    map_add' a b:=by unfold pairP; rw [map_add,Matrix.transpose_add, Matrix.mul_add, Matrix.add_apply]
    map_smul' r a:=by unfold pairP; rw [map_smul,Matrix.transpose_smul,Matrix.mul_smul,Matrix.smul_apply]; rfl
-- conditions
structure Fare(j:ℕ)(a b:ℝ){c f: Side}(g: Ratio c f)(J: Matrix (Co f θ) (Co c θ) ℝ)(F B:Bed) : Prop where
    up : ∃ R Q,Bank.TowerW j g F B J R Q
    saf: F.metric.safe
    strip : ∃ z:ℝ,0≤ z ∧ B.metric.strip z b
    floor : ∃ W:ℝ, Numeric (F.metric.acts f) a W ∧ Numeric (B.metric.acts c) a W
-- postL.J.K.b authority
structure Boat(j:ℕ)(a b:ℝ): Type where
    c:Side
    f:Side
    g:Ratio c f
    J:Matrix (Co f θ) (Co c θ) ℝ
    F:Bed
    B:Bed
    h : Fare j a b g J F B
private structure Axle(j:ℕ)(a b:ℝ):Type extends Boat j a b where
    x:Cover
    v:θ
    z:Co c δ
private lemma fare_roller (P:Parc)(hk: k+2 ≤ j)(hp:P∈tails ℓ k) (ha:0<a)(hb:0 ≤ b): ∃ C:ℝ,0≤ C ∧ ∀ m: Axle j a b, ‖(stalk m.f m.x m.v P*(m.J*d 1 m.c)) () m.z‖ ≤ C/ (m.g.count.val:ℝ)^(2+ℓ):=by
    let H:= Axle j a b; let z:=fun m:H=> billP m.f (m.J*d 1 m.c) m.x m.v m.z; let V:= fun m:H=> ((m.g.count.val:ℝ)^(2+ℓ))⁻¹
    simp_rw [div_eq_mul_inv]; rw [show (∃ C:ℝ,0≤ C ∧∀ m:Axle j a b, ‖_‖ ≤ _)= (∃ C:ℝ,0 ≤ C ∧∀ᶠ i in (⊤:Filter H), ‖z i P‖ ≤ C*V i) from propext (by simp only [eventually_top]; exact Iff.rfl)]
    refine Span.fellow z V ⊤ (Eventually.of_forall fun m=> inv_nonneg.mpr (pow_nonneg (side_pos ..).le ..)) (fun l hl hx x=>?_) P hp; obtain ⟨C,hc,h⟩:= Avalon.Worth.axial a b ha hb j l (by omega); refine ⟨C,hc,Eventually.of_forall fun m=>?_⟩
    obtain ⟨U,W,H⟩:= m.h.up; obtain ⟨w,hy,hm⟩:=m.h.floor
    change ‖(stalk m.f m.x m.v (strike l x) * (m.J*d 1 m.c)) () m.z‖ ≤ C/_; rw [stroke]; apply (h _ _ _ _ H m.h.saf m.h.strip hy ..).trans; gcongr; exact (by exact_mod_cast m.g.count.property: (1:ℝ)≤ m.g.count.val)
lemma priced (P:Parc)(hk:k+2≤j)(hp:P∈tails ℓ k)(ha:0<a)(hb:0≤b): ∃ C:ℝ,0≤C ∧ ∀ {c f:Side}(g: Ratio c f) (J: Matrix (Co f θ) (Co c θ) ℝ)(F B:Bed), Fare j a b g J F B → ∀ x:Cover,∀ v:θ,∀ z:Co c δ,
       ‖(stalk f x v P*(J*d 1 c)) () z‖ ≤ C/(g.count.val:ℝ)^(2+ℓ):=by
     obtain ⟨C,hc,h⟩:=fare_roller P hk hp ha hb; exact ⟨C,hc,fun {c f} g J F B h' x v z=>h ⟨⟨_,_,_,_,_,_,h'⟩,x,v,z⟩⟩
private structure Bulk (j:ℕ)(a b:ℝ): Type extends Boat j a b where
    x:Cover
    y:Cover
    i:θ
    i₂:θ
noncomputable def lakeU (g: Ratio c f)(J:Matrix (Co f θ) (Co c θ) ℝ)(B:Bed): Matrix (Co f θ) (Co f θ) ℝ:=J *learned B c * J.transpose
private lemma shores (P Q:Parc)(hk:k+2≤j)(hn:n+2≤j)(hp:P∈tails ℓ k)(ht:Q∈tails r n)(ha:0<a)(hb:0≤b):∃ C:ℝ,0≤ C ∧∀ m:Bulk j a b, ‖pairP m.f (lakeU m.g m.J m.B) m.x m.y m.i m.i₂ P Q‖ ≤ C/(m.g.count.val:ℝ)^(4+ℓ+r):= by
    let H:=Bulk j a b; let Z:=fun m:H=> lakeU m.g m.J m.B; let X:=fun m:H=> pairP m.f (Z m) m.x m.y m.i m.i₂; let Y:=fun m:H=> wishedL m.f (Z m) m.x m.y m.i m.i₂; let W:=fun m:H=> wishedR m.f (Z m) m.x m.y m.i m.i₂; let V:=fun m:H=> ((m.g.count.val:ℝ)^(4+ℓ+r))⁻¹
    simp_rw [div_eq_mul_inv]; rw [show (∃ C:ℝ,0 ≤ C∧∀ m:Bulk j a b, ‖_‖ ≤ _)= (∃ C:ℝ,0 ≤ C ∧∀ᶠ i in (⊤:Filter H), ‖X i P Q‖ ≤ C*V i) from propext (by simp only [eventually_top]; exact Iff.rfl)]
    refine Span.payments V ⊤ X Y W (fun _ _ _=>rfl) (fun _ _ _=>rfl) (Eventually.of_forall fun m=>inv_nonneg.mpr (pow_nonneg (side_pos ..).le ..)) (fun l hl hv x u hu hv' y=>?_) P hp Q ht; obtain ⟨C,hc,h⟩:= Warm.portrait a b ha hb j l u (by omega) (by omega); refine ⟨C,hc, Eventually.of_forall fun m=> ?_⟩
    obtain ⟨U,D,H⟩:= m.h.up; obtain ⟨w,hy,hm⟩:= m.h.floor
    unfold X pairP Z lakeU; rw [show stalk m.f m.x m.i (strike l x) * (m.J*learned m.B m.c*m.J.transpose)*(stalk _ m.y m.i₂ (strike u y)).transpose= stalk m.f m.x m.i (strike l x) *(m.J*learned m.B m.c)*(stalk _ m.y m.i₂ (strike u y) * m.J).transpose from by rw [transpose_mul]; simp only [Matrix.mul_assoc],couple,← Matrix.mul_assoc (Avalon.rocker m.f θ l)]
    change _≤ C/_; apply (h _ _ _ _ H m.h.saf m.h.strip hy hm ..).trans; gcongr; exact (by exact_mod_cast m.g.count.property: (1:ℝ)≤ m.g.count.val)
lemma rivers (P Q:Parc)(hk:k+2≤j)(hn:n+2≤j)(hp:P∈tails ℓ k)(ht:Q∈tails r n)(ha:0<a)(hb:0≤b):∃ C:ℝ,0≤ C ∧∀ {c f:Side}(g:Ratio c f)(J: Matrix (Co f θ) (Co c θ) ℝ)(F B:Bed), Fare j a b g J F B →∀ x y:Cover,∀ i v:θ, ‖pairP f (lakeU g J B) x y i v P Q‖ ≤ C/(g.count.val:ℝ)^(4+ℓ+r):=by
     obtain ⟨C,hc,h⟩:= shores P Q hk hn hp ht ha hb; exact ⟨C,hc,fun {c f} g J F B h' x y i v=>h ⟨⟨_,_,_,_,_,_,h'⟩,x,y,i,v⟩⟩
end YM.Bloom
#print axioms YM.Bloom.rivers
#print axioms YM.Bloom.priced
