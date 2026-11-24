import YM.Giles.Slat
/-! Combining T Bond and C-frame gauges.Wind exact even torus.Per convention.Phased. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.Frobenius TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s σ :ℝ}{c:Side}{n l d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals QCD.Bay Rudder
open Complex (exp I)
variable (g:su.Color)(F:Density c 6)(x y:Site c)(φ:Site c→ℝ)
noncomputable abbrev toneP(t:ℝ)(x:Site c):= Rudder.bird g (-t*φ x)
-- body probe after pure gradient links. Sign from slots.
noncomputable def sift (p: Flavor 6)(u v:Site c): G★→ₗ[ℂ]Bundle:= { toFun:=fun x=> QCD.Run.cell (piece p p (uncoat x)) u v,map_add':=fun A B=>by rw[map_add]; rfl,map_smul':=fun x y=>by rw [map_smul]; rfl }
local notation "ci" u:arg=>Lat.touch (colour u)
local notation "Y" => toneP g φ
local notation "B"=> touch (su.colorMat g)
lemma breeze (z:ℝ)(p: Flavor 6) (hP:SungP F): sift p x y (F (kiln g (z • glaze φ))) = ci (Y z x)* sift p x y (F 1) * star (ci (Y z y)):=by
     let k:= Y z; let L:=Lattice.gauge k (1:Grid c); have hp : kiln g (z • glaze φ)=L:=by nth_rw 1[←add_zero (z • glaze φ)]; rw [vapors,kiln0]
     let A:= siteRot k; let K:=rotates 6 k; rw [hp]; let V:=uncoat (F L); have hv: K*star K=1:= (rotates_law ..).2
     have he: uncoat (F 1)=star K*(V*K):=by rw [← hP k 1]; unfold Lat.slots; rw [sectX,Matrix.transpose_transpose]
     have hT:V=K* uncoat (F 1)*star K:=by rw[he,←mul_assoc K,hv,one_mul,mul_assoc,hv,mul_one]
     change QCD.Run.cell (piece p p V) x y= _ * QCD.Run.cell (piece p p (uncoat (F 1))) x y * star _; rw [hT]; unfold K Lat.rotates; rw [←copies_star,angie,angel]; unfold siteRot; rw [cell_ride_right,cell_ride_left]; rfl
lemma tell(h:SungP F)(he:Chart n F 1)(hn:1 ≤ n)(p:Flavor 6): sift p x y (tent g F (glaze φ))= (-φ x) • (B*sift p x y (F 1)) + φ y • (sift p x y (F 1)*B):=by
     let P:= sift p x y; let W:=glaze φ; let L:= P.toContinuousLinearMap.restrictScalars ℝ; let O(t:ℝ)(x:Site c): Bundle:=Lat.touch (colour (toneP g φ t x)); have h0(x:Site c): O 0 x=1:=by unfold O toneP; simp only [neg_zero,zero_mul,bird,zero_smul,su.mat_lieExp_zero, show colour 1=1 from rfl,touch_one]
     let M:Bundle:=touch (su.colorMat g); let T:ℝ→Site c→Bundle:=O
     have hm(x:Site c): HasDerivAt (fun t=>T t x) ((-φ x) • M) 0:=by
            let L: su.Mat →L[ℝ] Bundle:= LinearMap.toContinuousLinearMap { toFun:=fun i=>touch i,map_add':=fun A A1=> Matrix.kronecker_add ..,map_smul':=fun t A=> Matrix.kronecker_smul .. }
            have hv:HasDerivAt (fun t:ℝ=> -t*φ x) (-φ x) 0:=by simpa using! (hasDerivAt_neg (x:=(0:ℝ))).mul_const (φ x)
            have ht: HasDerivAt (fun x=> su.mat (Rudder.bird g x)) (su.colorMat g) (- (0:ℝ)*φ x):=by simp; have h:= Gall.fizz g 0; simp only[Rudder.bird,zero_smul, su.mat_lieExp_zero, su.mat_one,one_mul] at h; exact h
            rw [show (-φ x) • M=L ((-φ x) • su.colorMat g) from (L.map_smul _ _).symm]
            have hL:= L.hasFDerivAt.comp_hasDerivAt 0 (ht.scomp 0 hv); exact hL
     have hS: HasDerivAt (fun t:ℝ => P (F (kiln g (t • W)))) (L (tent g F W)) 0:=by
           let X:=F ∘ kiln g; have hc := collinear g 0 F (k:=n) (by rw[kiln0]; exact he)
           have hf:HasDerivAt (fun t:ℝ=>t • W) W 0:=by simpa using (hasDerivAt_id' (0:ℝ)).smul_const W
           have hv: HasFDerivAt X (tent g F) ((0:ℝ) • W):=by rw[zero_smul]; exact (hc.differentiableAt (by exact_mod_cast Nat.ne_of_gt hn)).hasFDerivAt
           have hL:= L.hasFDerivAt.comp_hasDerivAt 0 (hv.comp_hasDerivAt 0 hf); exact hL
     let Z:=P (F 1); have hr:= ((hm x).mul_const Z).mul (hm y).star
     rw [show (fun t:ℝ=> P (F (kiln g (t • W))))=(fun t:ℝ=> O t x *Z*star (O t y)) from funext fun t=> breeze g _ x y _ t p h] at hS; have hs:= hS.unique hr
     have he: star M= -M:=by rw [show M= touch (su.colorMat g) from rfl,touch_star,show star (show Mat from su.colorMat g)= - (show Mat from su.colorMat g) from su.colorMat_skew g]; exact by ext i j; change _*(-(_ :ℂ))= - (_ * (_:ℂ)); rw[mul_neg]
     change L _=_; rw [hs]; change ((-φ x) • M) * Z * star (O 0 y) + (O 0 x)*Z * star ((-φ y) • M)= (-φ x) • (M*Z)+ φ y • (Z*M); rw [h0,h0,star_one,one_mul,mul_one,smul_mul_assoc,star_smul,star_trivial,he,mul_smul_comm]; simp -- layout
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.tell
