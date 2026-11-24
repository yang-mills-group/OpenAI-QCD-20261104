import YM.Giles.Slat
/-! First-order total approximations before pure-gauge rewrite. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s σ :ℝ}{c:Side}{n l d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Complex (exp I)
open Tawny.Cast.Rays
variable (U:BudgetPoint)(g:su.Color)(a b:Axis)(T:TaperHol)(i j:Fiber)(p:Flavor 6)
noncomputable def yellow (i j:Fiber)(p:Flavor 6) (F:G★): (Site c →Site c→ℂ) →ₗ[ℂ]ℂ:= {
      toFun:=fun D=> reed p p i j D F
      map_add':=fun x y=>by unfold reed; simp[Pi.add_apply, mul_add,add_mul,Finset.sum_add_distrib]
      map_smul':=fun z x=>by unfold reed; simp_rw [LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply, smul_mul_assoc, RingHom.id_apply,Finset.smul_sum] }
local notation "Q"=> reed p p i j
local notation "Θ"=> tick c
local notation "ρ"=> helm c
local notation "λt"=> (0:Multi 10)
local notation "τ"=> T.T
noncomputable def chipS (p:Flavor 6) (u v:Multi d) (i j:Fiber) : Label d→ₗ[ℂ]ℂ:= { toFun:=fun x=>juncoat x.val ((u,i),p) ((v,j),p),map_add':=fun x y=> congr_fun (congr_fun (map_add juncoat x.val y.val) _) _,map_smul':=fun t x=> congr_fun (congr_fun (map_smul juncoat t x.val) _) _ }
noncomputable def point1(a:Axis)(p:Flavor 6)(i j:Fiber): Label 10→ₗ[ℂ]ℂ:= chipS p (leadR a) λt i j - chipS p λt (leadR a) i j
lemma strokeL (F G:Density c 6)(X:Label d)(h:Tally T 0 X F G) (x y:Multi d) (he:spinWeight x+spinWeight y≤d): Q (ballast x y T.T) (foil F G 1)=chipS p x y i j X:= (script T F G X h ((x,i),p) ((y,j),p) he).symm
lemma bracken (F G:Density c 6)(X:Label 10)(h:Tally T 0 X F G)(he:Allow U g (foil F G) n C):
     ‖river1 a p i j (foil F G)-point1 a p i j X‖≤ costQ 2*Θ*C:=by
    let Y:= foil F G 1; let M:= yellow i j p Y
    have hu:mu1 a T.T=ballast (leadR a) λt τ - ballast λt (leadR a) τ (c:=c):=by
        funext x y; unfold mu1 ballast; simp only [Pi.sub_apply,Nw,profile_0,profile_L,indexT]; push_cast; ring
    rw [point1,LinearMap.sub_apply,←strokeL T _ _ _ _ _ _ h _ _ (by rw [gradeL,gradeV]; norm_num),← strokeL T _ _ _ _ _ _ h _ _ (by rw [gradeL,gradeV]; norm_num)]
    change ‖ρ⁻¹ • (M _- M _) - (M _-M _)‖≤ _; rw[← map_sub,←map_smul,←map_sub M (ballast (leadR a) λt τ) _,←hu,←map_sub]; exact pupils Y p i j (he.heatL p i j) _ (exact1 a T.T) (mul_nonneg (costQ_p _ (by norm_num)) (tick_g c).le)
noncomputable def leaf2 (p:Flavor 6)(i j:Fiber)(g:su.Color)(a b:Axis) (T:Taper)(F:Density c 6):ℂ:= reed p p i j (mu2 a T) (tent g F (monoT b))+reed p p i j (ballast λt λt T) (tent g F (arcT a b))
set_option maxHeartbeats 360000 in
lemma gleam_h (hp: 2 ≤ U.power): ∃ C:ℝ,0≤C∧∀ c:Side,∀ F:Density c 6,∀ (n:ℕ)(D:ℝ), Allow U g F n D→∀ (i j: Fiber) (p:Flavor 6), ‖river2 a b p i j g F-leaf2 p i j g a b T.T F‖ ≤ C*tick c *D:=by
    obtain ⟨S,hS,hG⟩:= tithe U g _ (dart0 b) (Nat.zero_le _); obtain ⟨M,hM,hQ⟩:= tithe U g _ (dart1 a b) (by omega); obtain ⟨R,hR,hr⟩:= Chan_fare U g _ (brims a b) hp; refine ⟨costQ 1*S+(1+eCost)*M+R,by positivity[eC0,costQ_p 1 zero_le_one],fun c F n D hd i' j' p'=> ?_⟩
    let x:=rub g F; let V := monoT (c:=c) b; let X := arcT (c:=c) a b; let k:=x (waveZ 0 a b); let U:=tent g F X; let q:=helm c; let Y:= x (brim a b c); let A:=((tick c:ℝ)⁻¹:ℂ) • brim a b c; have ht:Y=(tick c:ℂ) • x A:=by rw[← map_smul]; unfold A; rw [smul_smul,mul_inv_cancel₀,one_smul]; exact_mod_cast (tick_g c).ne'
    have he: k=tent g F V:=by unfold k x; rw[era0,tune]
    
    let l:ℝ:= tick c; let B(t:Site c→Site c→ℂ):= reed p' p' i' j' t
    let υ:= B (seek2 1 a); let o:= seek2 (c:=c) 1 a; let o':= seek2 (c:=c) 0 a; let d:=(ballast (c:=c) λt λt T.T); let z:=mu2 (c:=c) a T.T
    let d1:= q⁻¹ • (o-o')-z; let h1:=B d1 k; let h2:= B (o-d) U; let h3:= B o Y
    have hQ1: ‖h1‖ ≤ costQ 1*l * (S*D):=by apply pupils k p' i' j' ?_ _ (exact2 a T.T) (mul_nonneg (costQ_p _ zero_le_one) (tick_g c).le); rw [he]; exact hG _ _ _ _ _ _ _ hd
    have hQ2: ‖h2‖ ≤ (1+eCost)*l * (M*D):= pupils U p' i' j' (hQ _ _ _ _ _ _ _ hd) _ (gentle2 T.T a) (mul_nonneg (by positivity[eC0]) (tick_g c).le)
    have hQ3: ‖h3‖ ≤ l*(R*D):= pupils Y p' i' j' (a:=l*(R*D)) (by rw [ht,p_scaled,Complex.norm_real,Real.norm_of_nonneg (tick_g c).le]; exact mul_le_mul_of_nonneg_left (hr _ _ _ _ _ _ _ hd) (tick_g c).le) _ (C:=1) (seek2_cap 1 a) zero_le_one |>.trans (le_of_eq (one_mul _))
    rw [show river2 a b p' i' j' g F-leaf2 p' i' j' g a b T.T F=h1+h2+h3 from ?_]; swap
    · have H : q⁻¹ • (x (waveZ 1 a b)-k)=Y+U:=by unfold k U x; unfold Y brim; change _=rub g F _ + _; rw[map_sub,map_smul,map_sub,tune]; unfold X; rw[sub_add_cancel] -- elliosis
      unfold river2 leaf2; change q⁻¹ *(B _ _ - B _ _) - (B _ (tent g F (monoT b))+B _ _)=_
      let Q₀:= yellow i' j' p' k
      let Q₁:= yellow i' j' p' U
      rw [show tent g F (monoT b)= k from he.symm]; have hp: B o k-B o' k= Q₀ (o-o'):= (map_sub Q₀ o o').symm
      have hy: q⁻¹*(B o (x (waveZ 1 a b))- B o k)=B o Y+B o U :=by change q⁻¹ • (B o (x (waveZ 1 a b))-B o k) = _; rw[←map_sub,←map_smul,H,map_add]
      have hh:B (o-d) U=B o U-B d U:=map_sub Q₁ o d
      have hk: B d1 k=q⁻¹*(B o k-B o' k)-B z k:=by change Q₀ _=_; unfold d1; rw [map_sub,map_smul,map_sub]; rfl
      unfold h1 h2 h3; rw [hh,hk]
      let A':=x (waveZ 1 a b); change q⁻¹*(B o A'-B o' k)-(B z k+B d U)= _; calc
            _= q⁻¹*(B o A'- B o k)+ q⁻¹*(B o k-B o' k)-(B z k+B d U):=by ring
            _=_:=by rw[show q⁻¹*(B o A'-_)=_ from hy]; ring
    apply (norm_add_le ..).trans; refine (add_le_add (norm_add_le ..) (le_refl _)).trans ((add_le_add (add_le_add hQ1 hQ2) hQ3).trans ?_); unfold l; apply le_of_eq; ring
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.gleam_h
#print axioms YM.Massive.Patria.Gall.bracken
