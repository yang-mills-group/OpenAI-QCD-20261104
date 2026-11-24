import YM.Mural.Weld
/-!
# Finite-hop path path control uniform after L for the birth.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Comet
open QCD QCD.Grass QCD.Finch QCD.Lat Lattice Wilson RG
open Function Finset MeasureTheory Filter Fork Laurent Flume Kit Pine
open scoped ContDiff BigOperators Matrix Matrix.Norms.L2Operator Classical Kronecker
open YM.Next.Free
variable {c f:Side}{j k m:ℕ}
-- vary once chord. all links in specified extent.
variable (x y p q:Site f)(g:Lat.Frame f)
variable {U:Grid f}{v t rV:ℝ}{B:ℕ}
lemma memv {V:Grid f}(x:Site f)(w:Walk) {r:ℝ}(hv:∀ i∈visits x w,∀ a:Axis, su.chord (V (i,a)) ≤r) : su.chord (travel V x w) ≤ w.length*r:=by
   induction w generalizing x with
   | nil=> simp [travel]
   | cons a w ih=>
      have hp: su.chord (travel V (x+a.vec) w)≤ w.length*r:= ih _ (fun i h=>hv _ (List.mem_cons_of_mem _ h))
      have hg : su.chord (a.read V x)≤r:=by
           cases a with | mk j p=> cases p; exact hv x (List.mem_cons_self) j; change su.chord _⁻¹ ≤r; rw [Gauge.chord_inv]; apply hv _ _ j; apply List.mem_cons_of_mem; rw [sub_eq_add_neg]; cases w <;> simp [visits,Step.vec]
      rw [travel]; apply (su.chord_triangle ..).trans; refine (add_le_add hg hp).trans_eq (?_); simp [add_mul,add_comm]
lemma vis_at (o:Site f)(w:Walk)(h: separation p o+w.length≤ B)(hv:∀ i:Site f,separation p i≤B→∀ a:Axis,su.chord (U (i,a))≤v): su.chord (travel U o w)≤w.length*v:=
   memv _ _ (fun i he=> hv _ ((separation_triangle ..).trans ((Nat.add_le_add_left (Eyrie.walked w o i he) _).trans h))) -- inference
lemma sig_path (w:Walk)(he: separation p x+w.length≤B)(hv:∀ i:Site f,separation p i≤B→∀ a:Axis, su.chord (U (i,a))≤v) (t:Site f)
   (hz:∀ X:su.El, ‖colour X-1‖≤ rV *su.chord X)(hr:0≤rV): ‖turn t U w x-turn t 1 w x‖≤ rV*(w.length*v):=by
   rw [zedTurn,turn,← smul_sub,norm_smul,nPrice,one_mul]; exact (hz _).trans (mul_le_mul_of_nonneg_left (vis_at p x w he hv) hr)
variable (P:Flight j k)(d:f.val=c.val*P.L.val)(x y:Site c)
local notation "J"=> arctic P.L j
local notation "L"=> P.L
set_option quotPrecheck false
local notation "S"=> (sliceL P d)
local notation "Xg"=> (sliceL P d).embed x
local notation "Yg"=> (sliceL P d).embed y
local notation "I"=> P.patch.Points
local notation "V"=> massL L
lemma near_coal (t:Site f)(hp:separation p Xg+ arctic P.L j ≤B)(h:∀ i:Site f,separation p i≤B→∀ a:Axis,su.chord (U (i,a))≤v)(hz:∀ X:su.El, ‖colour X-1‖≤ rV *su.chord X)(hr:0≤rV)(hv:0≤v) : ‖texel P d t x q U-texel P d t x q 1‖≤ V*(rV*(↑(arctic L j)*v)):=by
    let T:=byteV P d t x q; let p₀:= rV*(↑(arctic L j)*v)
    have he(i:I)(a:Lattice.Order): ‖edgeB P d t x q i a U-edgeB P d t x q i a 1‖≤ p₀:=by
        unfold edgeB; dsimp only; split; swap; · rw [sub_zero,norm_zero]; unfold p₀; positivity
        let w:= route 0 i.val a; have hh:w.length ≤ arctic P.L j:= stems ..
        refine (sig_path _ p _ ((Nat.add_le_add_left hh _).trans hp) h t hz hr).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hh) hv) hr)
    have hF(a:Lattice.Order): ‖T a U-T a 1‖≤ p₀:=by
        unfold T byteV; rw [← sum_sub_distrib]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=> P.patch.weight i*p₀) ?_).trans (le_of_eq ?_))
        · intro i _; rw [← smul_sub,norm_smul,Complex.norm_real,Real.norm_of_nonneg (P.patch.weight_nonneg _)]; exact mul_le_mul_of_nonneg_left (he i a) (P.patch.weight_nonneg _)
        rw [← sum_mul,P.patch.weight_sum,one_mul]
    unfold texel; rw [← smul_sub,← smul_sub, ← sum_sub_distrib,norm_smul, Complex.norm_real, Real.norm_of_nonneg (mass_pos _).le,norm_smul,norm_inv,Complex.norm_natCast]; apply mul_le_mul_of_nonneg_left _ (mass_pos _).le; refine ((mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum fun i _=>hF i)) (by positivity)).trans_eq (?_)) ; rw [sum_const,card_univ,nsmul_eq_mul,← mul_assoc,inv_mul_cancel₀ poll_pos.ne',one_mul]
-- Jan path. p,q Input, x,y output. In actual RG the AP phase is carried in `lightS`, not discarded. Keep window and proximity.
local notation "Tx"=> texel P d 0 x p
local notation "Ty"=> texel P d 0 y q
local notation "λx"=> lightS P d 0 x p
local notation "λy"=> lightS P d 0 y q
noncomputable def loaded (U:Grid f): Mat:= (texel P d 0 x p U)*apogee p q U*star (texel P d 0 y q U)
noncomputable def cleared (W:Grid c): Mat:= (lightS P d 0 x p*star (lightS P d 0 y q)) • apogee x y W
@[fun_prop] lemma loaded_c : Continuous (loaded p q P d x y):=by unfold loaded; fun_prop
@[fun_prop] lemma cleared_c : Continuous (cleared p q P d x y):=by unfold cleared; fun_prop
lemma met : loaded p q P d x y 1=cleared p q P d x y 1:=by unfold loaded cleared; rw [portrait P d,portrait P d,star_smul,star_one,remainsX,remainsX,mul_one]; rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,mul_smul]
lemma load_frame (U:Grid f): loaded p q P d x y (gauge g U)= colour (g Xg)* loaded p q P d x y U *star (colour (g Yg)):=by
    unfold loaded; rw [staffT,staffT,clot]; simp only [star_mul,star_star]; let a:=colour (g p); let b:=colour (g q)
    simp only [mul_assoc]; have hP(k:su.El)(x: Mat): star (colour k)*(colour k*x)=x:=by rw [←mul_assoc,show star (colour k) * colour k=(1:Mat) from su.mat_star_mul _,Matrix.one_mul]
    simp_rw [hP]
lemma clear_frame (W:Grid c)(g:Lat.Frame c) : cleared p q P d x y (gauge g W)= colour (g x)*cleared p q P d x y W *star (colour (g y)):=by rw [cleared,cleared,clot,Matrix.mul_smul, Matrix.smul_mul]
local notation "sV"=>Kit.scale L
variable (hB:2*P.patch.radius < f.val)
include hB
lemma load_bound (U:Grid f): ‖loaded p q P d x y U‖≤ Kit.scale L^2:=by
   unfold loaded; rw [pow_two]; refine (norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (lamp ..)).trans (entryL P d 0 x p U hB))) ((norm_star _).le.trans (entryL P d 0 y q U hB)) (norm_nonneg _) (scale_pos _).le)
lemma light_bound (t:Site f): ‖lightS P d t x p‖ ≤ Kit.scale L:=by
   have hp:=entryL P d t x p 1 hB; rw [portrait,norm_smul,Kit.oneNorm,mul_one] at hp; exact hp
lemma clear_bound (W:Grid c): ‖cleared p q P d x y W‖≤ Kit.scale L^2 :=by
    unfold cleared; rw [pow_two,norm_smul]; exact (mul_le_of_le_one_right (norm_nonneg _) (lamp ..)).trans (by rw [norm_mul,norm_star]; exact mul_le_mul (light_bound p P d x hB 0) (light_bound q P d y hB 0) (norm_nonneg _) (scale_pos _).le)
-- t0 stationary.Photo.JV. B.Clock controls. restrict `separation p small` etc. for all. afterL cost tom.
local notation "V0"=> loaded p q P d x y
local notation "W0"=> cleared p q P d x y
variable {i0:Site f}{M₁ M₂:ℕ}{r R:ℝ}
lemma pace {A B A' B':Mat}{a b y v:ℝ}(he:‖A-A'‖≤ y*r)(hp:‖B-B'‖≤ v*r)(ht:‖A‖≤ a)(hz:‖B'‖ ≤ b) (hr:0≤a): ‖A*B-A'*B'‖ ≤ (a*v+b*y)*r:=by
   rw [show A*B-A'*B'= A*(B-B')+(A-A')*B' from (by rw [mul_sub,sub_mul]; abel)]; refine (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul ht hp (norm_nonneg _) hr)) ((norm_mul_le ..).trans (mul_le_mul he hz (norm_nonneg _) ((norm_nonneg _).trans he)))).trans_eq (?_)); ring
lemma load_fit (U:Grid f) (o:Site f) (h: separation o Xg+arctic L j ≤B)(hx:separation o Yg+arctic L j≤B)(hq:separation o p+4*M₁ ≤B)(hu: separation p q≤ M₁) (hh:0 ≤ R) (hr:0 ≤ r)(hZ:∀ X:su.El,‖colour X-1‖≤ R*su.chord X)(hf:∀ i:Site f,separation o i≤ B →∀ a:Axis,su.chord (U (i,a)) ≤r):
     let C₀:=massL P.L*R*arctic P.L j
     ‖loaded p q P d x y U-loaded p q P d x y 1‖ ≤(Kit.scale L*C₀+Kit.scale L*(sV*(R*(4*M₁:ℕ))+1*C₀))*r:=by
       intro C₀; have h₁ : ‖Tx U-Tx 1‖≤ C₀*r:=(near_coal o p P d x 0 h hf hZ hh hr).trans_eq (by unfold C₀; ring)
       have h₂: ‖star (Ty U)-star (Ty 1)‖≤ C₀*r:=by rw [← star_sub,norm_star]; exact (near_coal o q P d y 0 hx hf hZ hh hr).trans_eq (by unfold C₀; ring)
       let W:=apogee p q; have hF: ‖W U-W 1‖≤ (R*(4*M₁:ℕ))*r:=by
           rw [show W 1=1 from remainsX ..]; have hx:(cord p q).length ≤ 4*M₁:= cord_len p q hu
           exact (hZ (travel U p (cord p q))).trans ((mul_le_mul_of_nonneg_left ((vis_at o p (cord p q) ((Nat.add_le_add_left hx _).trans hq) hf).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hx) hr)) hh).trans_eq (mul_assoc ..).symm)
       unfold loaded; refine pace P hB (pace P hB h₁ hF (entryL P d 0 x p U hB) (lamp p q 1) (scale_pos _).le) h₂ ?_ ((norm_star _).le.trans (entryL P d 0 y q 1 hB)) (scale_pos _).le -- implic hB in pace. 
       exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (lamp p q U)).trans (entryL P d 0 x p U hB))
end YM.QCD.Comet
#print axioms YM.QCD.Comet.vis_at
#print axioms YM.QCD.Comet.load_fit
