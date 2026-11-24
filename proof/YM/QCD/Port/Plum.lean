import YM.QCD.Port.Terra
/-! # exact fixed-U re-spending. Retain tagged covariances for gauge. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Tree
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra AtomF Sway OrbitG ConnectedActivityE6 Push.AbsoluteSums Footprint Jets.Touch Pressure
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {f c:Side}{F:ℕ}{u v η ξ t p C D A R z q w γ Ω π κ B:ℝ}{b m i a:ℕ}{j k:ℕ}{L:Flight j k}{J:Plan k}{H:f.val=c.val*L.L.val}{X:St f}{W:ℕ→Atom su 2} {V:Grid f}
local notation "Mx"=> Modes c F
local notation "S"=> sliceL L H
variable (P : Swathe L H X W J u v η p q b)
lemma priceD (V:Grid f)(h: Species L H u A v η B i X) : (X V).det= (Real.exp (Real.log (X V).det.re):ℂ):=by
 rw [Real.exp_log (h.full _)]; exact (Cost.determinant_real chi_sq (h.crease _)).symm
lemma sky_first (x:ℂ)(F:ℕ): exp (sparkF c F x)= Complex.exp x • (1:EvenA c F):=by
   change exp (_)=_; rw [sparkF,show x • (1:EvenA c F)= algebraMap ℂ (EvenA c F) x from (Algebra.algebraMap_eq_smul_one x).symm]
   rw [← map_exp (algebraMap ℂ (EvenA c F)) _ x,Complex.exp_eq_exp_ℂ] -- direction
   · exact Algebra.algebraMap_eq_smul_one ..
   exact continuous_algebraMap ℂ _
lemma moonlit (t:ℝ)(F:ℕ): exp (sparkF c F (↑F*(↑t:ℂ))) = (↑(Real.exp t):ℂ)^F • (1:EvenA c F):=by rw [sky_first, Complex.exp_nat_mul,Complex.ofReal_exp]
-- roll shirt exp gauss mismatch integrates.
lemma ore (x : Grid f)(a':ℝ)(F m:ℕ) (h:Species L H u A v η B i X):
   (X x).det^F • ((↑(Real.exp (- Extra.Iteration.action W x)):ℂ)^F • gauss (Lat.copies F (foam L H X x)))=
   (X 1).det^F • (light _ (∑ i : Finset (Varn f c),∏ j∈i,broke P F m j x) * gauss (Lat.copies F (wood J 0 L.land (lowC S x)))):=by
   let W':= wood J 0 L.land (lowC S x); have hK:=valueW P F m x h
   let d:=Real.log (X x).det.re-Real.log (X 1).det.re-Extra.Iteration.action W x; let Q:= foam L H X x
   have hp : Q= -(dusk L H J X x)+W':=by unfold dusk; simp only [Pi.sub_apply,neg_sub, sub_add_cancel]; exact (sub_add_cancel _ _).symm -- Q expand
   have he:=congr_arg exp hK; rw [NormedSpace.exp_add, moonlit, flicker _ univ, show ∀ T:Type,∀(_ : Fintype T), (univ:Finset T).powerset=univ from fun _ _=>by ext; simp] at he
   rw [show (∑ i : Finset (Varn f c),∏ j∈i,broke P F m j x)=_ from he, map_mul, map_smul,map_one, light_exp,serviceP, ← gauss, Algebra.smul_mul_assoc, one_mul]
   rw [show foam L H X x = _ from hp, show Lat.copies F (-(dusk L H J X x)+W')=Lat.copies F _+Lat.copies F W' from Matrix.blockDiagonal_add _ _, gauss_add]
   rw [smul_mul_assoc]
   let y:=Extra.Iteration.action W x; let ξ:=gauss (Lat.copies F (-(dusk L H J X x)))*gauss (Lat.copies F W'); change _=(X 1).det^F • ((↑(Real.exp d):ℂ)^F • ξ)
   simp_rw [smul_smul, ← mul_pow]; refine congr_arg (fun v:ℂ=>v^F • ξ) ?_; rw [priceD x h,priceD 1 h]; norm_cast; rw [← Real.exp_add,← Real.exp_add]; unfold d; ring_nf -- ok
variable {E K: Type} [Countable E][Countable K] (Z:Rise f F E K)
def starPerf (L:Flight j k)(H:f.val=c.val*L.L.val)(v:St f) (F:ℕ)(x : Grid f) := Lat.copies F (v x -(tied L H 0 x)ᴴ*tied L H 0 x) -- actually Delta
lemma sprig (F:ℕ)(x:Grid f)(X:St f): Lat.copies F (X x)=starPerf L H X F x+(ater L H x)ᴴ*ater L H x:=by
   unfold starPerf ater; rw [← choir_star,← choir_mul]; have h:= Matrix.blockDiagonal_sub (fun _ : Flavor F=> X x) (fun _=> ((tied L H 0 x)ᴴ*tied L H 0 x)); rw [show Lat.copies F (X x-(tied L H 0 x)ᴴ*tied L H 0 x)=Lat.copies F (X x)- choir F ((tied L H 0 x)ᴴ*tied L H 0 x) from h, sub_add_cancel]
lemma spool (x:Grid f)(F:ℕ)(h:Species L H u A v η B i X): 1-ater L H x*(Lat.copies F (X x))⁻¹*(ater L H x)ᴴ=Lat.copies F (foam L H X x):=by
  unfold ater; rw [← choir_star,← Jets.linked _ _ (h.sole x), ← replicas]; rw [← choir_mul,← choir_mul]
  unfold foam; unfold inverser; have ht:= Matrix.blockDiagonal_sub (fun _ : Flavor F=> (1: Sheet c)) (fun _=> tied L H 0 x*(X x)⁻¹*(tied L H 0 x)ᴴ); rw [← copies_one F]; exact ht.symm
lemma f_total (x:Grid f) (g: Sun L c f H v u A η C a X)(m:ℕ)(T:Fj (Tr f) E K→Support c) (hpC:Count (g.equip F m) Z T)(ht:Z.Wave t) (hv:Placid Z t x) :
   let Q := g.equip F m
   (↑(Real.exp (-Extra.Iteration.action W x)):ℂ)^F • sheath 1 (ater L ‹f.val=c.val*L.L.val› x) (gauss (starPerf L ‹f.val=c.val*L.L.val› X F x)*Z.bluff t x)= (X 1).det^F •
     (light _ ((∑' w,Cove.caller Q Z t T x w) * ∑ i:Finset (Varn f c),∏ j∈i,broke P F m j x) * gauss (Lat.copies F (wood J 0 L.land (lowC S x)))):=by
   intro Q
   let h':f.val=c.val*L.L.val:= ‹f.val=c.val*L.L.val›; let θ (x:Grid f):= Lat.copies F (X x); let L':= (fun U => starPerf L h' X F U+(ater L h' U)ᴴ*ater L h' U)
   have he:L'=θ:=funext fun i=>(sprig F i X).symm
   have hh:IsUnit (θ x).det:= by rw [show _=(X x).det^F from copies_det ..]; exact (g.stable.sole _).pow _
   have hp:= push_fermi Q Z t hpC (ater L h') (starPerf L h' X F) x ht (show Q.Cast (ater L h') L' from he.symm ▸ (committed g F m)) (show IsUnit (L' x).det from he.symm ▸ hh) hv
   dsimp only at hp; rw [← sprig] at hp; rw [hp,spool x F g.stable,copies_det, map_mul,mul_assoc]
   rw [smul_comm, ← mul_smul_comm, ← mul_smul_comm, ore P x 0 F m g.stable, mul_smul_comm] -- shape
end YM.QCD.Port
