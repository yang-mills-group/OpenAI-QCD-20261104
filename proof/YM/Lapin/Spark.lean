import YM.Lapin.Kite
import YM.Lapin.Kroft
/-! row inspection to approximate by constant link on second axis. first variation.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny Tawny.Cast.Rays
variable {D:ℝ}{c:Side}{n l d m r k p q w i N:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC Patria Patria.Depth Patria.Rolls PCAC.Oren QCD.Entr.Goals
variable {S:Scheme}{R:Side}(A:Massive.Run S N R 6)(hA:A.Actual)(hi:i≤ N)
local notation "M"=> S.side R i
variable (a b:Flavor 6) (s t:Axis)(g:su.Color)(e:ℤ)(u:Averaging)(j j':Fiber)(T:TaperHol)(U:BudgetPoint)
local notation "φ"=> A.density i
local notation "G"=> marque (i:=i) A true a s
local notation "Γ"=>ms (i:=i) a A
local notation "P"=> rayC φ a
local notation "W"=> report A Γ u i 0
local notation "Y"=> foil φ W
local notation "B"=> touch (su.colorMat g)
local notation "J"=> wave (gamma (0:Axis))
local notation "L"=> (0:Multi 10)
local notation "M!"=> (Rod M T.T t P)
local notation "Ω" => ballast L L T.T
variable (hk:1 ≤ k)(hv:IsUnit (A.density i 1))
include hk hi hA hv
lemma read_t (hY:Chart k Y 1): reed a a j j' (ballast L L T.T) (tent g Y (Gall.glaze (indexT t)))=(J*M!*B) j j':=by
       have he:SungP Y:=treated _ _ (dSung A hA hi) (by rw[arrivesHere]; exact m_sight A hA a hi)
       let v:= Y; have hh(x y): sift a x y (v 1)= if x=0 then J*Run.cell P x y else 0 := prismT A hA a u 1 hi hv x y
       let f(x y:Site M):= Ω x y * ((indexT t y:ℝ):ℂ); let g'(x y:Site M):= Ω x y * ((-indexT t x:ℝ):ℂ)
       rw [roll_p g _ _ _ _ _ _ hY he hk,show hit a Y f= J*M! from ?_,show hit a Y g'=0 from ?_,mul_zero,zero_add] -- pattern synt.M cost.F is let
       · unfold hit; refine sum_eq_zero fun z _=>sum_eq_zero fun j _=>?_; rw [hh]; split; next hm=>
              unfold g'; rw [hm,show indexT t (0:Site (S.side R i))=0 from (by simp[indexT,Lattice.lift])]; simp
         next _=>exact smul_zero _
       change (∑ x:Site M,∑ y: Site M, f x y • (sift a x y (v 1)))=J* ∑ y:Site M,_
       rw[sum_eq_single (0:Site M), Matrix.mul_sum]; apply sum_congr rfl; intro i _; rw [hh,if_pos rfl,Matrix.mul_smul]; unfold f; rw [originX,βδ,one_mul,N_one]; unfold indexT; norm_cast -- ring
       intro x _ h; exact sum_eq_zero fun i _=>by rw [hh,if_neg h,smul_zero]
       simp
omit hk hi hA hv
-- wave difference scaled by helm jointly, direct Chan with inverse tick. avoids second
local notation "K"=> tick
local notation "Gξ" c:arg=> (↑((tick c)⁻¹:ℝ):ℂ) • (waveZ (c:=c) 1 s t - waveZ 0 s t)
lemma kray : Chan 1 (fun c=>Gξ c):=by
      refine ⟨1,zero_le_one,fun c i=>?_⟩; simp only [Pi.smul_apply,Pi.sub_apply,waveZ,gaze_nil]; let z:= i.1; rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (tick_g _).le), one_mul,peg,pow_one]; split_ifs with h; swap; · simp; positivity
      unfold gaze; simp only[Int.cast_one,one_mul]; apply le_trans (mul_le_mul_of_nonneg_left (pointζ_first ..) (inv_nonneg.mpr (tick_g _).le)); rw [norm_mul,Real.norm_of_nonneg (tick_g _).le, inv_mul_cancel_left₀ (tick_g c).ne']; exact ((liftN ..)).trans (le_add_of_nonneg_left zero_le_one)
local notation "O2"=> oracle2 1 s t
local notation "T2"=> reed a a j j'
lemma purseT (hp:2 ≤ U.power) : ∃ C:ℝ,0 ≤ C∧∀ c:Side,∀ (F: Density c 6)(n:ℕ)(aP:ℝ), Allow U g F n aP →∀ a j j', ‖O2 a j j' g F-reed a a j j' (ballast L L T.T) (tent g F (Gall.glaze (indexT t)))‖ ≤ (tick c+(c.val:ℝ)⁻¹)*C*aP:=by
       obtain ⟨S,hS,hP⟩:= Chan_fare U g _ (kray s t) (by omega); obtain ⟨V,hV,hX⟩:= tithe U g _ (nightF T.T t) hp; obtain ⟨Q,hQ,hF⟩:= tithe U g (fun c=>monoT (c:=c) t) (dart0 t) (Nat.zero_le _); refine ⟨S+(1+eCost)*Q+V,by positivity[eC0],fun c F n aP h a j k=> ?_⟩
       let o:=monoT (c:=c) t; let l:=tick c; let w:ℝ:= (c.val:ℝ)⁻¹; have ha:0 ≤ aP:= (peaks_g ..).trans (h.heatL a j k); have hw:0 < w:=by unfold w; positivity
       let x:=tent g F o; let A:= reed a a j k (c:=c); let K':=ballast L L T.T (c:=c); let p:=seek2 (c:=c) 1 s; let vT:=rub g F (Gξ c)
       let G₁:Cray c:= (glaze (indexT t)); let U':= tent g F ((c.val:ℝ) • (o-G₁))
       have ht: rub g F (waveZ 1 s t)=x+(l:ℂ) • vT:=by
            have he:= (tick_g c).ne'; unfold x o; rw[← tune,←era0 s t]; unfold vT; rw [map_smul,map_sub,smul_smul,show (l:ℂ)*↑((tick c)⁻¹)=1 from (by unfold l; norm_cast; field_simp),one_smul,add_sub_cancel]
       have hd:‖A p vT‖ ≤ S*aP:=(pupils _ _ _ _ (hP c F _ _ _ _ _ h) _ (seek2_cap 1 s) zero_le_one).trans (le_of_eq (one_mul ..)); have hv:‖A K' U'‖ ≤ V*aP:=(pupils _ _ _ _ (hX c F _ _ _ _ _ h) _ (banner1 (c:=c) _ t).2 zero_le_one).trans (le_of_eq (one_mul ..)) -- possible operand shadow vT.H var
       have hj: A p x-A K' x=A (p-K') x:= (map_sub (yellow _ _ _ x) p K').symm; have he:‖A p x- A K' x‖ ≤ ((1+eCost)*l)*(Q*aP):=hj ▸ pupils x _ _ _ (hF c _ _ _ _ _ _ h) _ (gentle2 _ s) (mul_nonneg (by positivity[eC0]) (tick_g _).le)
       have hh: x-tent g F G₁=(w:ℂ) • U':=by unfold U'; rw [Complex.coe_smul,← map_smul,smul_smul,inv_mul_cancel₀ (by positivity),one_smul,map_sub]
       rw [oracle2,ht]; let v:= tent g F G₁; change ‖A p _ - A K' v‖ ≤ _; rw[map_add,map_smul,show A p x+(l:ℂ) • A p vT-A K' v=(l:ℂ) • A p vT+((A p x-A K' x)+A K' (x-v)) from (by rw [map_sub]; abel), show x-v=(w:ℂ) • _ from hh, map_smul]; apply (norm_add_le ..).trans; apply (add_le_add_right (norm_add_le ..) _).trans; rw [norm_smul,norm_smul,Complex.norm_real,Complex.norm_real, Real.norm_of_nonneg (tick_g c).le,Real.norm_of_nonneg hw.le]; apply (add_le_add (mul_le_mul_of_nonneg_left hd (tick_g c).le) (add_le_add he (mul_le_mul_of_nonneg_left hv hw.le))).trans; change l*_+(_+w*_) ≤ (l+w)*_* _; have hℓ:0≤ l:= (tick_g c).le; have hQ:0≤(1+eCost)*Q:=mul_nonneg (by positivity[eC0]) hQ; nlinarith [show 0 ≤ w*(S*aP) from by positivity,show 0≤w*((1+eCost)*Q)*aP from by positivity, show 0 ≤ l* (V*aP) from by positivity ]
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.purseT
#print axioms YM.Massive.Patria.Gall.read_t
