import YM.Gall.Vices
/-! Move color-singlet moment prices. Grade d↦ d+2 tests selected. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat PCAC QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open Tawny.Cast.Rays
variable {u t a D C v e s:ℝ}{c:Side}{n l d m r w b:ℕ}{U:BudgetPoint}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas
open QCD.Entr.Goals
-- prism0 linear probe compiled from TALLY
variable (p q:Multi d)(T:TaperHol)(x:Cover)(k:Axis)(g:Flavor 6)(i j:Pinor)
local notation "K"=> step (S:=ℤ) k
noncomputable def loaf (p q:Multi d)(g:Flavor 6)(i j:Pinor) : Label d→ₗ[ℂ]ℂ:= {
    toFun:=fun X=>Tawny.Cast.prism0 g p q X.val i j,map_add':=fun A B=>by change (Tawny.Cast.prism0 _ _ _ (A.val + B.val)) i j= _; rw[map_add]; rfl,map_smul':=fun z A=>by change (Tawny.Cast.prism0 _ _ _ (z • A.val)) i j= _; rw[map_smul]; rfl }
noncomputable def ballast (p q:Multi d)(T:Taper) (u v:Site c):ℂ:= Nw T p u*Nw T q v
noncomputable def readG (g:Flavor 6)(i j:Pinor)(F:Site c→Site c→ℂ) := reed g g (i,0) (j,0) F
local notation "L"=> readG (c:=c) g i j
local notation "wℓ"=> T.T
local notation "δR"=> (1/2:ℝ)
lemma scan (X Y:Density c 6)(u:Label d)(h:Tally T 0 u X Y)(hp: spinWeight p+spinWeight q≤d): loaf p q g i j u=readG g i j (ballast p q wℓ) (foil X Y 1):=script T X Y u h ((p,i,0),g) ((q,j,0),g) hp
lemma syrupV (X Y:Density c 6)(h:IsUnit (X 1))(ht: march x X=X): L (ballast p q wℓ) (foil X (march x Y) 1)=L (syrup wℓ p q x) (foil X Y 1):=by
     let A:=foil X Y 1; have hs(Lz:Cover)(y: Density c 6)(hp:march x X=X):∀ u v:Site c, let t:= wrap c x; let M:=QCD.Run.cell (piece g g (uncoat (foil X y 1))) u v; QCD.Run.cell (piece g g (uncoat (foil X (march x y) 1))) (u+t) (v+t)= (heat x u*heat x v) • M:=by
          intro u v z M; rw[ambassador X y x h hp]; exact thug (Canvas.foil X y) u v x
     let D(u v:Site c):=uncoat A ((u,i,0),g) ((v,j,0),g)
     let t:= wrap c x
     let V:=Equiv.addRight t; change (∑ i:Site c,∑ j:Site c, _)= ∑ u:Site c,∑ v:Site c,syrup wℓ p q x u v*D u v -- edit
     rw[←Equiv.sum_comp V]; apply sum_congr rfl; intro b _; rw [←Equiv.sum_comp V]; apply sum_congr rfl; intro a _; have ht : uncoat (foil X (march x Y) 1) (((b+t),i,0),g) (((a+t),j,0),g)=(heat x b*heat x a)*D b a:=by exact congr_fun (congr_fun (hs 0 Y (by assumption) b a) (i,0)) (j,0)
     rw [show uncoat (foil X (march x Y) 1) ((V b,i,0),g) ((V a,j,0),g)= _ from ht]; unfold ballast syrup; change Nw wℓ p (b+t)* Nw wℓ q (a+t) * ( _*D b a)= _; ring
noncomputable def proceeds (g:Flavor 6)(i j:Pinor)(p q:Multi d)(T:Taper)(k:Axis)(X:G★):ℂ:= δR • (readG g i j (beamT T p q (step k)) X-readG g i j (beamT T p q (-(step k))) X)
noncomputable abbrev port (a:ℝ)(T:Side)(v:ℝ):= (80/(T.val:ℝ))*(a/v^2)
lemma instant (F G:Density c 6)(Q:Label d) (he: Tutor 0 U (foil G F) v n m a)(hP:Tally T 0 Q G (stunt k F))(hv:0<v)(hm:2 < m)(hn:3 ≤ n)(hh:∀ x:Cover, march x G=G)(hd:d≤10)(hp:spinWeight p+spinWeight q≤d): ‖loaf p q g i j Q- proceeds g i j p q wℓ k (foil G F 1)‖ ≤ port a c v:=by
    rw [scan p q T g i j _ _ Q hP hp]; let A(x:Cover):= foil G (march x F) 1; let Y:= foil G F 1; let Sw(x:Cover):=L (syrup wℓ p q x) Y; let t(x:Cover):=L (beamT wℓ p q x) Y
    rw [show foil G _ 1=δR • (A K-A (-K)) from ?_]; swap
    · change Ring.inverse (G 1)*(δR • (march K F 1-march (-K) F 1))=(1/2:ℝ) • (Ring.inverse (G 1)* (march K F 1)-Ring.inverse (G 1)*(march (-K) F 1)); rw[mul_smul_comm,mul_sub]
    let J:= L (ballast p q wℓ); rw [show J _ =δR • (J (A K)-J (A (-K))) from (by rw [←map_sub]; exact (J.restrictScalars ℝ).map_smul δR _),show J (A K)= _ from syrupV p q T K _ i j _ _ hP.unit.self_of_nhds (hh _),show J (A (-K))=_ from syrupV p q T (-K) _ i j _ _ hP.unit.self_of_nhds (hh _)]
    have h(x:Cover)(hh:Nearby x): ‖Sw x-t x‖ ≤ port a c v:= grains p q wℓ x g g (i,0) (j,0) (foil G F) he hv hh (by unfold spinWeight at hp; omega) hn hm
    change ‖δR • (Sw _-Sw _)-δR • (t _-t _)‖ ≤ _; rw [←smul_sub,show Sw K-Sw (-K) -(t K-t (-K))=(Sw K-t K)-(Sw (-K)-t (-K)) from by abel, norm_smul, Real.norm_of_nonneg (by norm_num)]
    exact (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (h K ⟨k,.inl rfl⟩) (h (-K) ⟨k,.inr rfl⟩))) (by norm_num : 0 ≤ (δR:ℝ))).trans_eq (by ring)
lemma entire (V W:Site c→Site c→ℂ)(F:G★): L (V+W) F=L V F+L W F:=by unfold readG reed; simp [Pi.add_apply,add_mul,sum_add_distrib]
lemma entire_diff (V W:Site c→Site c→ℂ)(F:G★): L (V-W) F=L V F - L W F:=by unfold readG reed; simp [Pi.sub_apply,sub_mul,sum_sub_distrib]
lemma entire_s (V:Site c→Site c→ℂ)(F:G★)(s:ℝ): L (s • V) F=s • L V F:=by unfold readG reed; simp_rw [LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,Finset.smul_sum, smul_mul_assoc]
lemma entire_c (V:Site c→Site c→ℂ)(F:G★)(s:ℂ): L (s • V) F=s • L V F:=by unfold readG reed; simp_rw [LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,Finset.smul_sum,smul_mul_assoc]
lemma notice (F:G★): proceeds g i j p q T.T k F= L (δR • (beamT wℓ p q K-beamT wℓ p q (-K))) F:=by rw [entire_s,entire_diff]; rfl
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.instant
#print axioms YM.Massive.Patria.Gall.notice
