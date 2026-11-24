import YM.Massive.Lining.Portage
/-! # All orientations at finite spacing; samplers tested also through AP seams. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Lining.Temper
open QCD QCD.Lat Lattice Wilson Massive.Papyrus UV Filter Function Finset Matrix Grass
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators NNReal Classical Kronecker TensorProduct
open Purl Scan Cylinder Paper TensorProduct Ferry
variable {H:Source.Hol su}{d h:ℕ} (F:Flag H d h)(U: Kedge H d h)(t:Finset Cover) (n:Side)(b: Cover)
local notation "Q" => SpinMode d
local notation "T" => Nearest t 6
local notation "Y" => Modes n 6
variable (V:Grid n)
abbrev anchored (n :Side)(b:Cover)(V:Grid n): Land:= expandAt (wrap n b) V
def flower (v:Grid n): Matrix Q Y ℂ:= start U t (anchored n b v)*belt n t b
def dartSpin (v:Grid n) : SpinPol d→ₐ[ℂ] Lat.Fields n 6:= adapter (flower U t n b v) (Mstar (flower U t n b v))
def valley (v : Grid n): GPol→ₐ[ℂ]ℂ:= Labels.read (extraction F (anchored n b v))
def dart (v:Grid n): Pol d→ₗ[ℂ] Lat.Fields n 6:=(TensorProduct.lid ℂ _).toLinearMap.comp (TensorProduct.map (valley F n b v).toLinearMap (dartSpin U t n b v).toLinearMap)
lemma dart_at(x:GPol)(y:SpinPol d): dart F U t n b V (x ⊗ₜ[ℂ] y)=valley F n b V x • dartSpin U t n b V y:=by rw [dart,LinearMap.comp_apply,TensorProduct.map_tmul]; rfl -- `lid_tmul`
lemma dart_ship (x: Pol d): adapter (belt n t b) (belt n t b) (glaze F U t (anchored n b V) x)=dart F U t n b V x:=by
   induction x using TensorProduct.induction_on with
   | zero=> simp
   | tmul p q=> rw [dart_at,stencil,map_smul]; unfold valley dartSpin flower ink; rw [adapt_together,mstar_mul,belt_star]
   | add p q hp hq=> simp_rw [map_add,hp,hq]
variable (s: Signed)
lemma flow_pin (ht:Parade t)(p:EuPin)(hp:p.Lifts s)(M : Spike): flower U t n b (pull s 0 V)*Action.moved s M= turned p (wave M) * flower U t n (s.act b) V:=by
   let W:=anchored n (s.act b) V; unfold flower; rw [show anchored n b (pull s 0 V)=scene s W from Ferry.wind n b s V,Matrix.mul_assoc,Ferry.sails _ _ _ _ ht M,← Matrix.mul_assoc,mobile U W s ht p hp M, Matrix.mul_assoc]
lemma flow_opp (ht: Parade t)(p:EuPin)(hp:p.Lifts s)(M:Spike) : Mstar (flower U t n b (pull s 0 V))*Action.moved s M = turned p (wave M)* Mstar (flower U t n (s.act b) V):=by
   let W:=anchored n (s.act b) V; unfold flower; rw [show anchored n b (pull s 0 V)=scene s W from Ferry.wind n b s V,mstar_mul,mstar_mul,belt_star,belt_star,Matrix.mul_assoc,Ferry.sails _ _ _ _ ht,← Matrix.mul_assoc,mobile_star U W s ht p hp M, Matrix.mul_assoc]
lemma valley_pin (g:GPol): valley F n b (pull s 0 V) g= valley F n (s.act b) V (Labels.rotated s.ortho g):=by
    let W:=anchored n (s.act b) V; unfold valley; rw [show anchored n b _=scene s W from Ferry.wind n b s V]; unfold extraction; rw [Labels.rotated,Labels.eval_changed,F.stove,sendJet] -- ok 
def shipP (p:EuPin): Lat.Fields n 6→ₐ[ℂ]Lat.Fields n 6:= adapter (Action.moved s p.matrix⁻¹.val) (Action.moved s p.matrix.val.transpose)
lemma wind_echo (ht: Parade t)(p:EuPin)(hp:p.Lifts s)(x: Pol d) : shipP n s p (dart F U t n b (pull s 0 V) x)=dart F U t n (s.act b) V (pinAct p x):=by
   induction x using TensorProduct.induction_on with
   | zero=>simp
   | tmul x y=> rw [pinAct,TensorProduct.map_tmul,dart_at,dart_at,map_smul,valley_pin,show p.coord=s.ortho from hp]; simp only [AlgHom.toLinearMap_apply]; unfold dartSpin shipP; rw [adapt_together,adapt_together,flow_pin U t n b V s ht p hp, flow_opp U t n b V s ht p hp]
   | add x y hx hy=> simp_rw [map_add,hx,hy]
variable (k:Frame n)
lemma valley_gauge(g:GPol) : valley F n b (gauge k V) g=valley F n b V (dyesG (k (wrap n b)) g):=by
   unfold valley; rw [show anchored n b (gauge k V)=gaugeF (k ∘ gain n b) (anchored n b V) from Ferry.ferry_stretch n b k V]; unfold dyesG; rw [Labels.eval_changed,extraction,F.color,Function.comp_apply, gain,zero_add,tinted, ← sendJet]
lemma flow_gauge : flower U t n b (gauge k V)* Lat.rotates 6 k = colorTable (k (wrap n b))* flower U t n b V:=by
   unfold flower; rw [show anchored n b (gauge k V)=gaugeF (k ∘ gain n b) (anchored n b V) from Ferry.ferry_stretch n b k V]; rw [Matrix.mul_assoc,Ferry.ferries n t b k,← Matrix.mul_assoc,gauging,Function.comp_apply,Ferry.gain,zero_add, Matrix.mul_assoc]
lemma flow_gauge_o : Mstar (flower U t n b (gauge k V))*Mstar (Lat.rotates 6 k) = Mstar (colorTable (k (wrap n b)))* Mstar (flower U t n b V):= by rw [←mstar_mul, ←mstar_mul,flow_gauge]
private lemma wind_gauge_spin (y:SpinPol d): slots 6 k (dartSpin U t n b (gauge k V) y)= dartSpin U t n b V (adapter (colorTable (k (wrap n b))) (Mstar (colorTable (k (wrap n b)))) y):=by unfold slots dartSpin; rw [adapt_together,adapt_together, flow_gauge]; rw [← mstar_sq, flow_gauge_o]
lemma wind_gauge(x:Pol d) : slots 6 k (dart F U t n b (gauge k V) x)=dart F U t n b V (colorAct (k (wrap n b)) x):=by
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul x y=> rw [colorAct,TensorProduct.map_tmul,dart_at,dart_at,map_smul,valley_gauge]; rw [wind_gauge_spin]; rfl
    | add x y hx hy=> simp_rw [map_add,hx,hy]
end YM.Massive.Lining.Temper
#print axioms YM.Massive.Lining.Temper.wind_gauge
