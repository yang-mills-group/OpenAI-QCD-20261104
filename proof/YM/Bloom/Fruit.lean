import YM.Bloom.Pearl
/-! # spins finite stage actual operations. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bloom
open Function Lattice Laurent Bloch Metric RG Filter Arise
open Finset YM.Bank Precision Matrix YM.Bloom
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator
open QCD QCD.Lat QCD.Free QCD.Flume QCD.Bank Next.Free
variable {c f:Side}{j k m n l ℓ r:ℕ}
noncomputable def chargeP (f:Side)(J:Kit.Rail f c) (x:Cover)(i:Fiber)(v:Lat.Row c): Parc→ₗ[ℝ]ℂ where
    toFun P:=(plume f x i P*J) () v
    map_add' a b:=by rw [map_add,Matrix.add_mul,Matrix.add_apply]
    map_smul' a x:=by rw [map_smul,Matrix.smul_mul,Matrix.smul_apply]; rfl
noncomputable def pairS(f:Side)(J:Sheet f) (x y:Cover)(i j:Fiber)(P Q:Parc):ℂ:=(plume f x i P*J*(plume f y j Q)ᴴ) () ()
noncomputable def waryL (f:Side)(J:Sheet f)(x y:Cover)(i j:Fiber)(Q:Parc): Parc→ₗ[ℝ]ℂ where
    toFun P:=pairS f J x y i j P Q
    map_add' a b:=by unfold pairS; rw [map_add,Matrix.add_mul,Matrix.add_mul, Matrix.add_apply]
    map_smul' r a:=by unfold pairS; rw [map_smul,Matrix.smul_mul,Matrix.smul_mul,Matrix.smul_apply]; rfl
noncomputable def waryR (f:Side)(J:Sheet f)(x y:Cover)(i j:Fiber)(P:Parc): Parc→ₗ[ℝ]ℂ where
    toFun Q:=pairS f J x y i j P Q
    map_add' a b:=by unfold pairS; rw [map_add,conjTranspose_add,Matrix.mul_add,Matrix.add_apply]
    map_smul' r a:=by unfold pairS; rw [map_smul,conjTranspose_smul,Matrix.mul_smul,Matrix.smul_apply]; rfl
structure Fish(j:ℕ) where
    c : Side
    f : Side
    g : Ratio c f
    D : Train j
    B : Train j
    U : Kit.Rail f c
    X : Kit.Rail c f
    h : ∃ Q,Bank.Giant j g D B U X Q
    x : Cover
    a : Fiber
private structure Polar(j:ℕ) extends Fish j where
    Z : Kit.Rail f c
    z : Lat.Row c
    hz : Z=U ∨ Z=Xᴴ
lemma gear_low (m:Side)(h:r ≤ n): gear m n ≤ gear m r:=by
    unfold gear; have hp := Kit.slope_pos m; gcongr; exact_mod_cast m.property
private lemma valve (P:Parc)(hp:P∈tails ℓ k)(ht:k+2≤j):∃ C:ℝ,0≤ C ∧∀ m:Polar j, ‖(plume m.f m.x m.a P*m.Z) () m.z‖ ≤ C*gear m.g.count ℓ:=by
     let H:=Polar j; let Z:=fun m:H=>chargeP m.f m.Z m.x m.a m.z; let V:=fun m:H=>gear m.g.count ℓ; rw [show (∃ C:ℝ,0≤ C ∧∀ m:H, ‖_‖ ≤ _)= (∃ C:ℝ,0 ≤ C ∧∀ᶠ i in (⊤:Filter H), ‖Z i P‖ ≤ C*V i) from propext (by simp only [eventually_top]; exact Iff.rfl)]
     refine Span.fellow Z V ⊤ (Eventually.of_forall fun m=> (gear_pos ..).le) (fun l hl hm x=> ?_) P hp
     obtain ⟨C,hc,H'⟩:=Bank.aval (j:=j) (by omega) l (by omega); refine ⟨C,hc,Eventually.of_forall fun m=>?_⟩; obtain ⟨Q,h⟩:=m.h; have hh:=H' _ _ _ h (wrap m.f (m.x+x),m.a) m.z
     change ‖(plume m.f m.x m.a (strike l x)*m.Z) () m.z‖ ≤ _; rw [windT, norm_mul,pathLength, one_mul]; cases m.hz with|inl he=> rw [he]; exact hh.1.trans (mul_le_mul_of_nonneg_left (gear_low _ hl) hc)|inr he=>rw [he]; exact hh.2.trans (mul_le_mul_of_nonneg_left (gear_low _ hl) hc)
lemma valves (P:Parc)(hp:P∈tails ℓ k)(ht:k+2≤j):∃ C:ℝ,0≤ C ∧∀ {c f:Side} (g: Ratio c f)(F B:Train j){U X Q},Giant j g F B U X Q → ∀ x a z,
    ‖(plume f x a P*U) () z‖ ≤ C*gear g.count ℓ ∧ ‖(plume f x a P*Xᴴ) () z‖ ≤ C*gear g.count ℓ:=by
       obtain ⟨C,hc,h⟩:= valve P hp ht; refine ⟨C,hc,fun {c f} g F B {U X Q} G x a z=> ?_⟩; exact ⟨h ⟨⟨c,f,g,F,B,U,X,⟨Q,G⟩,x,a⟩,U,z,Or.inl rfl⟩, h ⟨⟨c,f,g,F,B,U,X,⟨Q,G⟩,x,a⟩,Xᴴ,z,Or.inr rfl⟩⟩ -- underscores?
private structure Lad(j:ℕ) extends Fish j where
     y : Cover
     b : Fiber
noncomputable def fuelS (g: Ratio c f)(U: Kit.Rail f c)(X: Kit.Rail c f)(B:Train j): Sheet f:= U*stage B c*X
private lemma cruise (P Q:Parc)(hp:P∈tails ℓ k)(ht:Q∈tails r n)(hk:k+2≤j)(hn:n+2≤j): ∃ C:ℝ,0≤ C ∧∀ m:Lad j, ‖pairS m.f (fuelS m.g m.U m.X m.B) m.x m.y m.a m.b P Q‖ ≤ C*(gear m.g.count ℓ*gear m.g.count r):=by
     let H:= Lad j; let K:=fun m:H=> fuelS m.g m.U m.X m.B; let X:=fun m:H=> pairS m.f (K m) m.x m.y m.a m.b; let Y:=fun m:H=> waryL m.f (K m) m.x m.y m.a m.b; let W:=fun m:H=> waryR m.f (K m) m.x m.y m.a m.b; let V:=fun m:H=>gear m.g.count ℓ * gear m.g.count r
     rw [show (∃ C:ℝ,0≤ C ∧∀ m:Lad j, ‖_‖ ≤ _)=(∃ C:ℝ,0≤ C ∧∀ᶠ i in (⊤:Filter H), ‖X i P Q‖ ≤ C*V i) from propext (by simp only [eventually_top]; exact Iff.rfl)]
     refine Span.payments V ⊤ X Y W (fun _ _ _=>rfl) (fun _ _ _=>rfl) (Eventually.of_forall fun m=> mul_nonneg (gear_pos ..).le (gear_pos ..).le) (fun l hl hv x u hu hv' y=>?_) P hp Q ht
     obtain ⟨C,hc,H'⟩:=spin_echo (j:=j) (by omega) l u (by omega) (by omega); refine ⟨C,hc, Eventually.of_forall fun m=>?_⟩
     obtain ⟨R,hm⟩:=m.h
     let D:=plume m.f m.x m.a (strike l x); let F:=plume m.f m.y m.b (strike u y); let Z:=stage m.B m.c
     unfold X pairS K fuelS; rw [show D*(m.U*Z*m.X)*Fᴴ =D*m.U*Z*(F*m.Xᴴ)ᴴ by rw [conjTranspose_mul, conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc]]; unfold D F; rw [sells,norm_mul,norm_mul,pathLength,pathLength,one_mul,one_mul]; apply (H' _ _ _ hm ..).trans; unfold V; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul (gear_low _ hl) (gear_low _ hu) (gear_pos ..).le (gear_pos ..).le) hc
lemma mariner (P Q:Parc)(hp:P∈tails ℓ k)(ht:Q∈tails r n)(hk:k+2≤j)(hn:n+2≤j): ∃ C:ℝ,0≤ C ∧∀ {c f:Side}(g:Ratio c f)(D B:Train j){U X R}, Giant j g D B U X R→ ∀ x y a b, ‖pairS f (fuelS g U X B) x y a b P Q‖ ≤ C*(gear g.count ℓ*gear g.count r):=by
      obtain ⟨C,hc,h⟩:= cruise P Q hp ht hk hn; refine ⟨C,hc,fun {c f} g D B {U X R} H x y a b=> h ⟨⟨c,f,g,D,B,U,X,⟨R,H⟩,x,a⟩,y,b⟩⟩
end YM.QCD.Bloom
#print axioms YM.QCD.Bloom.mariner
#print axioms YM.QCD.Bloom.valves
