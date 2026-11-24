import YM.QCD.Globe.Glaze
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
open Nola
variable {a b x t:ℝ}(X:EvenA c N)
def GrassA (X: EvenA c N)(t:ℝ)(n:ℕ)(a:ℝ):Prop:= band locationP X.val t n ≤ Fintype.card (Site c)*a
lemma downsR (o z:Site c)(h:Cocoa X): soilH locationP X.val t m z=soilH locationP X.val t m (z+o):=by
     let P:=ports N o; let H:=portS N o; let A:=Equiv.addRight o
     have he(i: Finset (Keys c N)): edges locationP (i.image H)= (edges locationP i).image A:=by unfold edges; rw [image_image,image_image]; apply image_congr; intro j _; exact portAt o N j
     have hy(S:Support c): Nola.reel (S.image A)=Nola.reel S:=by unfold Nola.reel; rw [sup_image]; simp_rw [sup_image]; exact congr_arg (Finset.sup S) (funext fun i=>congr_arg (Finset.sup S) (funext fun j=>separation_translate i j o)) -- edit
     let V i:=if z+o∈edges locationP i then grainH locationP X.val t m i else 0
     change _=∑ i,V i; rw [← Equiv.sum_comp H.finsetCongr]; apply sum_congr rfl; intro i _; unfold V
     have hQ : H.finsetCongr i=i.image H:= map_eq_image ..
     have hv : (i.image H).card=i.card:=card_image_of_injective _ H.injective
     simp only [hQ,grainH, hv, he, show ‖coef (i.image H) X.val‖=‖coef i X.val‖ from Cocoa.away o X h i, Nola.tell,hy];
     have hp: z+o∈ image (⇑A) (edges locationP i)↔ z∈ edges locationP i:=by change A z∈_↔ _; simp
     simp only [hp]
lemma GrassA.fetch (hp:GrassA X (2*t) m a)(h:Cocoa X)(ht:0<t)(o:Site c): soilH locationP X.val t m o ≤ a:=by
    let g:= soilH locationP X.val t m; have he(z: Site c):g z=g o:=by nth_rw 1 [show z=o+(z-o) from by abel]; exact (downsR X (z-o) o h).symm

    have hh : (∑ i,g i) = (Fintype.card (Site c):ℝ)*g o:=by simp_rw [fun i=>he i]; rw [sum_const,card_univ,nsmul_eq_mul]
    apply le_of_mul_le_mul_left _ (show 0<(Fintype.card (Site c):ℝ) by positivity); apply le_trans _ hp; change (Fintype.card (Site c):ℝ)*g o≤ _; rw [← hh]; unfold g soilH band; rw [sum_comm]; apply sum_le_sum; intro i _;
    rw [← sum_filter,sum_const,nsmul_eq_mul]; unfold grainH; have hz : (↑((univ.filter (fun x=> x∈edges locationP i)).card):ℝ) ≤ (2:ℝ)^i.card:=by
         have hz':(edges locationP i).card ≤ i.card:= card_image_le; rw [show univ.filter (fun x=> x∈ edges locationP i) = edges locationP i from ?_];
         · exact_mod_cast hz'.trans (Nat.lt_pow_self (by omega : 1 < 2)).le
         ext; simp
    apply (mul_le_mul_of_nonneg_right hz (grains locationP X.val ht (m:=m) i)).trans ; rw [mul_pow]; unfold grainH; apply le_of_eq; ring
lemma GrassA.invert {Y:EvenA c N} (hz: GrassA X t m a)(hp:∀ i,‖coef i Y.val‖ ≤ ‖coef i X.val‖)(ht:0<t): GrassA Y t m a:=by
      apply le_trans _ hz; apply sum_le_sum; intro i _; unfold grainH; gcongr; exact zero_le_one.trans (tell_one ..); exact hp i
lemma raze (v:Finset (Keys c N)): coef v (Stew.stage j X).val=if v.card=j then coef v X.val else 0:=angel j v X.val
noncomputable abbrev oilD (X:EvenA c N) := X-Stew.stage 0 X
noncomputable def peakZ (X:EvenA c N):= oilD X-Stew.stage 2 X
def Pure (X:EvenA c N):Prop:=∀ i:Finset (Keys c N), i.card < 4→ coef i X.val=0
lemma forged : Pure (peakZ X):=by
     intro i hi; unfold peakZ; change coef i (X.val-(Stew.stage 0 X).val-(Stew.stage 2 X).val)=_; rw [map_sub,map_sub,raze,raze]; by_cases hp:i.card=2; · rw [hp]; simp
     by_cases he:i.card=0; · rw [he]; simp
     rw [if_neg hp,if_neg he,measured i (by omega) X]; abel
-- cross charge apply approxim. dimensions
end YM.QCD.Globe
