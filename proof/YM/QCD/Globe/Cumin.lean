import YM.QCD.Globe.Gumbo
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
variable {X Y:Sheet c}{A C t W:ℝ}
-- direct commutator estimates
noncomputable def stupa (o: Site c): Sheet c:= rides (Equiv.refl _) (fun i=> (separation o i:ℂ) • 1)
def Rset (o:Site c)(X:Sheet c) := X*stupa o-stupa o*X
lemma rakeZ (X:Sheet c)(x y o:Site c): cell (Rset o X) x y= ((separation o y:ℂ)-separation o x) • cell X x y:=by
    have he(Z:Sheet c)(p:Site c→Bundle): cell (Z*rides (Equiv.refl _) p) x y=cell Z x y*p y:=by
       nth_rw 1 [← star_star (rides (Equiv.refl _) p)]; rw [ride_ad, cell_ride_right, star_star]; rfl
    unfold Rset stupa; rw [show ∀ A B:Sheet c,cell (A-B) x y=cell A x y-cell B x y from fun _ _=> rfl,he,cell_ride_left,Equiv.refl_apply,sub_smul, Matrix.smul_mul,Matrix.mul_smul,mul_one,one_mul]
noncomputable def rake (o:Site c) : ℕ→ Sheet c→ Sheet c
    | 0=> id
    | n+1=> rake o n ∘ Rset o
lemma rake_cost (hp: Beam X k A)(hk:m≤k)(hA:0 ≤ A)(p:Site c):‖rake p m X‖ ≤ A:=by
    let V:=rake p m X
    have H(x y:Site c): Run.cell V x y=((separation p y:ℂ)-separation p x)^m • cell X x y:=by
       suffices hx:∀ (j:ℕ)(X:Sheet c), Run.cell (rake p j X) x y=((separation p y:ℂ)-separation p x)^j • Run.cell X x y by exact hx m _
       intro j; induction j with
       | zero=>simp[rake]
       | succ j ih=> intro X; rw [rake,Function.comp_apply,ih,rakeZ,smul_smul,pow_succ]
    let f (x y:Site c):=costS k x y * ‖cell X x y‖
    refine Run.wind_op hA V f (fun x y => ?_) hp.toR (fun i => ?_ )
    · rw [H,norm_smul,norm_pow]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply le_trans (pow_le_pow_left₀ (norm_nonneg _) (show ‖(separation p y:ℂ)-(separation p x:ℂ)‖≤ 1 + separation x y from ?_) m) (pow_le_pow_right₀ (by simp) hk);
      have hx : (separation p y:ℝ)≤ separation p x+separation x y:=by exact_mod_cast separation_triangle p x y
      have hy: (separation p x:ℝ)≤ separation p y+separation x y:=by exact_mod_cast (separation_triangle p y x).trans_eq (by rw [separation_comm y x])
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real]; apply abs_le.mpr; constructor <;> linarith
    have hh:=hp.axR i; unfold Gan at hh; simp_rw [cell_flip,norm_star,id_eq,cost_symm i] at hh; exact hh
lemma rake_leg (X Y:Sheet c)(p: Site c):Rset p (X*Y)=Rset p X*Y+X*Rset p Y:=by unfold Rset; noncomm_ring
lemma rake_h (X Y: Sheet c)(p:Site c): rake p m (X+Y)=rake p m X+rake p m Y:=by induction m generalizing X Y with
   | zero=>rfl
   | succ m ih=> simp only [rake,Function.comp_apply]; rw [show Rset p (X+Y)=Rset p X+Rset p Y from ?_,ih]; unfold Rset; noncomm_ring
lemma rake_j (X: Sheet c)(p:Site c): rake p m (-X)=-rake p m X:=by induction m generalizing X with
   | zero=>rfl
   | succ m ih=> simp only [rake,Function.comp_apply]; rw [show Rset p (-X) = -Rset p X from ?_,ih]; unfold Rset; noncomm_ring
lemma plumer (x y: Sheet c)(z:ℕ)(s:Site c)(h:∀ i≤z,‖rake s i x‖≤ A)(he:∀ i≤z,‖rake s i y‖≤ C)(hz:0 ≤ A) : ‖rake s z (x*y)‖ ≤ 2^z*(A*C):=by
    induction z generalizing x y with
    | zero=> rw [pow_zero,one_mul]; have hx : ‖x‖≤A:=h 0 le_rfl; have hh:‖y‖≤ C:=he 0 le_rfl; change ‖x*y‖≤_; exact (norm_mul_le x y).trans (mul_le_mul hx hh (norm_nonneg y) hz)
    | succ z ih=>
         have hh(i:ℕ)(hi:i≤z): ‖rake s i (Rset s x)‖≤ A:=by have hr:=h (i+1) (by omega); rwa [rake,Function.comp_apply] at hr
         have ht(i:ℕ)(hi:i≤z): ‖rake s i (Rset s y)‖≤ C:=by have hr:=he (i+1) (by omega); rwa [rake,Function.comp_apply] at hr
         rw [rake,Function.comp_apply,rake_leg,rake_h]; exact (norm_add_le ..).trans ((add_le_add (ih (Rset s x) y hh (fun i hi=>he _ (by omega))) (ih x (Rset s y) (fun i hi=>h _ (by omega)) ht)).trans_eq (by rw [pow_succ]; ring))
lemma borage (X: Sheet c)(o:Site c)(hp:IsUnit X.det): Rset o X⁻¹=-(X⁻¹*Rset o X*X⁻¹):=by
    unfold Rset; rw [mul_sub, sub_mul, ← Matrix.mul_assoc X⁻¹ X, Matrix.nonsing_inv_mul _ hp, Matrix.one_mul, ← Matrix.mul_assoc X⁻¹, Matrix.mul_assoc _ X, Matrix.mul_nonsing_inv _ hp, Matrix.mul_one]; abel
lemma shack (a b:ℝ)(he:0≤ a)(hb:0≤b)(m:ℕ):∃ C:ℝ,0≤ C ∧∀ i≤ m,∀ (c:Side)(X:Sheet c), Beam X m a→ ‖X⁻¹‖≤b→ IsUnit X.det →∀ o:Site c,‖rake o i X⁻¹‖≤ C:=by
     suffices h:∀ j≤ m,∃ C:ℝ,0 ≤ C∧∀ (c:Side)(X:Sheet c),Beam X m a→‖X⁻¹‖≤ b→ IsUnit X.det→∀ i≤j,∀ o:Site c, ‖rake o i X⁻¹‖ ≤ C by obtain ⟨C,hC,H⟩:=h m le_rfl; exact ⟨C,hC,fun i hi n X h v w p=> H n X h v w i hi p⟩
     intro j; induction j with
     | zero=>
        intro hi; refine ⟨b,hb,fun c X hp hA hv i hi=>?_⟩
        obtain rfl:i=0:=by omega
        exact fun _=> hA
     | succ j ih=>
        intro hj; obtain ⟨C,hC,H⟩:= ih (by omega)
        let v:=2^j*(C*a); let w:=2^j*(v*C); refine ⟨max C w,hC.trans (le_max_left ..),fun c X hp hA hz i hi o=>?_⟩; by_cases ht:i ≤ j; · exact (H _ _ hp hA hz _ ht o).trans (le_max_left ..)
        obtain rfl:i=j+1:=by omega
        rw [rake, Function.comp_apply, borage _ o hz,rake_j,norm_neg]; have h(i)(hi:i≤ j):‖rake o i (X⁻¹*Rset o X)‖ ≤ v:=(plumer _ _ _ _ (fun j hj=> H _ _ hp hA hz j (le_trans hj hi) o) (fun j hk=>rake_cost hp (m:=j+1) (by omega) he o) hC).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (show (1:ℝ)≤2 by norm_num) hi) (mul_nonneg hC he))
        exact (plumer (X⁻¹*_ : Sheet c) X⁻¹ j o h (fun j hj=>H _ _ hp hA hz j hj o) (by unfold v; positivity)).trans (le_max_right ..)
end YM.QCD.Globe
