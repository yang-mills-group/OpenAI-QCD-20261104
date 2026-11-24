import YM.MassiveBridge.SpinStar

/-!
# RealSpin extension on exactly the filtered field multiplets

Use the polynomial coefficient continuation witnessed by label-space comparisons.
No finite-dimensional Lie classification or analytic extension axiom.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge
open Set Filter Function Mink Complex
open MassiveTwoEstimates (SpinGeometry.geometry)
open MassiveTwoEstimates.BoostMotion (point)
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
local notation "timev" => timeAxis

structure WSpins (F:Fields) where
  spin : RealSpin →* (F.W ≃ₗ[ℂ] F.W)
  lives d p x (h : x ∈ F.level d) : spin p x ∈ F.level d
  continuous_spin (v : F.W) : Continuous (fun p : RealSpin => spin p v)
  spatial (p : EuPin) (h : Lorentz.spatialTurn p.coord) (q : RealSpin)
      (t : q.coord = Lorentz.room p.coord h) (e : q.matrix=p.matrix) : spin q = F.action p
  boost (i : SpaceAxis) p (hp : RealSpin.Path i p) v : HasDerivAt (fun t=> spin (p t) v)
      ((-Complex.I) • F.lie (Ortho.plane timev i.castSucc) v) 0
  conjugate q v : spin q (F.adj timeAxis v) = F.adj timeAxis (spin q v)
  parity q v : spin q (F.parity v) = F.parity (spin q v)
  graded (q : RealSpin)(h:q.coord=1)(hg:q.matrix= -1): spin q=F.parity
  entire (r : Ray) (d:ℕ)(x : F.level d) : ∃ f : ℂ → F.level d, Differentiable ℂ f ∧ ∀ t : ℝ, (f (↑t:ℂ)).val = spin (point r t) x.val

namespace Spinor
open UV
variable {C : Sequence} {P : Calibration C} {F : Fields} {B : Bases F} {T : Momentum F} (E : F.System P) (H : B.Content P T)
-- Instances within filtered levels
abbrev Wd (F:Fields) (d:ℕ) := ↥(F.level d)
example (d : ℕ) : NormedSpace ℝ (Wd F d) := inferInstance

private lemma covering (d:ℕ)(x:Wd F d):∃ y: Label d, B.frame 0 d (UV.Free.projection y)=x :=by
   obtain ⟨z,rfl⟩:= (B.frame 0 d).surjective x
   obtain ⟨y,rfl⟩:= UV.Free.onto z; exact ⟨y,rfl⟩

include E H
lemma writes (d : ℕ) (s : Wd F d) (q : Module.Dual ℂ (Wd F d)) : Lettering (fun p => q (⟨F.action p s.val,E.lift _ s.property p⟩ : Wd F d)):=by
   obtain ⟨z,rfl⟩:= covering (B:=B) d s
   let G := @LinearMap.leftInverse ℂ (Label d) (UV.Pol d) _ _ _ _ _ (labels d).subtype
   let f := (((q.comp (B.frame 0 d).toLinearMap).comp (UV.Free.projection (d:=d))).comp G)
   refine (Vertex.figures z.val f).congr ?_; intro p
   rw [← P.sym.pinActs d p z]
   unfold f G; rw [LinearMap.comp_apply,show (labels d).subtype.leftInverse (P.sym.pin d p z).val = P.sym.pin d p z from LinearMap.leftInverse_apply_of_inj (labels d).ker_subtype _]
   exact congr_arg q (Subtype.ext (H.equivariant 0 d p z))

private lemma meets (d:ℕ) : ∃ g : ArrayS → Module.End ℂ (Wd F d), (∀ v, Differentiable ℂ fun p=> g p v) ∧ ∀ p v, ((g (printS p) v).val)=F.action p v.val :=by
   haveI := E.finite d
   classical
   let Z:= Module.finBasis ℂ (Wd F d)
   choose Y hY HY using (show ∀ i j, Lettering (fun p => Z.coord j (⟨F.action p (Z i).val,E.lift _ (Z i).property p⟩ : Wd F d)) from fun i j => writes E H d _ _)
   let g (A:ArrayS):= Z.constr ℂ (fun j=>∑ i, Y j i A • Z i)
   have he (A:ArrayS)(j) : g A (Z j)=∑ i,Y j i A • Z i:=Z.constr_basis ..
   have ht (s:EuPin)(j) : (g (printS s) (Z j)).val=F.action s (Z j).val:=by
      rw [he]; simp_rw [HY]; exact congr_arg Subtype.val (Z.sum_repr _)
   refine ⟨g,fun x=>?_,fun s x=>?_⟩
   · rw [← Z.sum_repr x]; simp_rw [map_sum,map_smul,he]
     apply Differentiable.fun_sum; intro i _
     have hi : Differentiable ℂ fun t=>∑ j,Y i j t • Z j:=Differentiable.fun_sum (u:=Finset.univ) fun j _=>(hY i j).smul (differentiable_const (Z j))
     exact hi.const_smul (Z.repr x i)
   conv_lhs=> rw [← Z.sum_repr x]
   change (F.level d).subtype _=_
   have hx := congr_arg (F.level d).subtype (Z.sum_repr x)
   conv_rhs=> rhs; change (F.level d).subtype x; rw [← hx]
   simp only [map_sum,map_smul]; exact Finset.sum_congr rfl fun i _=> congr_arg ((Z.repr x i) • ·) (ht s i)

def script (d:ℕ) := (meets E H d).choose
lemma prepares (d:ℕ) (p:EuPin) (x:Wd F d) : (script E H d (printS p) x).val=F.action p x.val := (meets E H d).choose_spec.2 p x
lemma diff_frame (d:ℕ)(x:Wd F d) : Differentiable ℂ fun p=> script E H d p x := (meets E H d).choose_spec.1 _
def levelAct (d:ℕ)(g:RealSpin) : Module.End ℂ (Wd F d) := script E H d (wire g)
lemma level_one (d:ℕ)(x:Wd F d): levelAct E H d 1 x=x:=Subtype.ext (by
   have he : wire 1=printS 1:=Prod.ext Maxwell.Free.stencil_one rfl
   rw [levelAct,he,prepares]; simp)
lemma level_mul (d:ℕ)(p q:RealSpin)(x:Wd F d): levelAct E H d (p*q) x=levelAct E H d p (levelAct E H d q x):=by
   haveI := E.finite d
   let U:= script E H d
   have h(s:EuPin): U (track (printS s) (wire q)) x=U (printS s) (U (wire q) x):=
      genuine q _ _ ((diff_frame E H d x).comp (track_left _)) ((LinearMap.toContinuousLinearMap (U (printS s))).differentiable.comp (diff_frame E H _ x)) (by
        intro t; change U (track (printS s) (printS t)) x=U _ (U _ x); rw [links]; apply Subtype.ext; unfold U; simp only [prepares,map_mul]; rfl)
   unfold levelAct; rw [← wires]
   exact genuine p _ _ ((diff_frame E H d x).comp (track_right _)) (diff_frame E H d (U (wire q) x)) h
lemma compatibility {d e:ℕ} (he:d≤e)(p:RealSpin)(x:Wd F d): Submodule.inclusion (E.increases he) (levelAct E H d p x)=levelAct E H e p (Submodule.inclusion (E.increases he) x):=by
   haveI:=E.finite d; haveI:=E.finite e
   exact genuine p _ _ ((LinearMap.toContinuousLinearMap (Submodule.inclusion (E.increases he))).differentiable.comp (diff_frame E H d x)) (diff_frame E H _ _) (by
      intro q; apply Subtype.ext; change (script E H d _ _).val = _; rw [prepares,prepares]; rfl)

private def reading (p:RealSpin) (x : F.W) : F.W := (levelAct E H (E.exhaustive x).choose p ⟨x,(E.exhaustive x).choose_spec⟩).val
private lemma read_in (d:ℕ)(p:RealSpin) (x:Wd F d): reading E H p x.val=(levelAct E H d p x).val:=by
   let k:=(E.exhaustive x.val).choose
   have h:= (E.exhaustive x.val).choose_spec
   let y : Wd F k:=⟨x.val,h⟩
   change (levelAct E H k p y).val= _
   rcases le_total k d with H'|H'
   · exact congr_arg Subtype.val (compatibility E H H' p y)
   exact congr_arg Subtype.val (compatibility E H H' p x) |>.symm

local notation "Lr" => levelAct E H
private def stream (g:RealSpin): Module.End ℂ F.W where
   toFun x:=reading E H g x
   map_add' x y:=by
      obtain ⟨d,hd⟩:= E.exhaustive x; obtain ⟨e,he⟩:=E.exhaustive y
      let m:=max d e; let u:Wd F m:= ⟨x,E.increases (le_max_left ..) hd⟩; let v:Wd F m:= ⟨y,E.increases (le_max_right ..) he⟩
      change reading E H g (u+v).val=reading E H g u.val + reading E H g v.val; rw [read_in,read_in,read_in,map_add]; rfl
   map_smul' t x:=by
      obtain ⟨d,hd⟩:= E.exhaustive x; let u:Wd F d:=⟨x,hd⟩
      change reading E H g (t • u).val=t • reading E H g u.val; rw [read_in,read_in,map_smul]; rfl
lemma stream_one: stream E H 1=LinearMap.id :=by
   ext1 x; obtain ⟨d,hd⟩:= E.exhaustive x; let u:Wd F d:=⟨x,hd⟩
   change reading E H _ u.val=u.val; rw [read_in,level_one]
lemma stream_mul (p q:RealSpin): stream E H (p*q)=(stream E H p).comp (stream E H q):=by
   ext1 x; obtain ⟨d,hd⟩:= E.exhaustive x; let u:Wd F d:=⟨x,hd⟩
   change reading E H (p*q) u.val=reading E H p (reading E H q u.val); rw [read_in,read_in,read_in,level_mul]

def venture (p:RealSpin): F.W≃ₗ[ℂ] F.W:= LinearEquiv.ofLinear (stream E H p) (stream E H p⁻¹)
   (by rw [← stream_mul, mul_inv_cancel,stream_one])
   (by rw [← stream_mul, inv_mul_cancel,stream_one])
def route : RealSpin →* (F.W≃ₗ[ℂ] F.W) where
   toFun p:=venture E H p
   map_mul' p q := LinearEquiv.toLinearMap_injective (stream_mul E H p q)
   map_one' := LinearEquiv.toLinearMap_injective (stream_one E H)
local notation "R" => route E H
lemma reading_at (p: RealSpin)(d:ℕ)(x:Wd F d) : R p x.val=(Lr d p x).val := read_in E H d p x
lemma life (p:RealSpin)(d:ℕ) (x:F.W) (h:x∈F.level d) : R p x∈ F.level d := (reading_at E H p d ⟨x,h⟩).symm ▸ (Lr d p ⟨x,h⟩).property
lemma continuous_route (x:F.W): Continuous fun p=>R p x:=by
   obtain ⟨d,h⟩:= E.exhaustive x; let y:Wd F d:=⟨x,h⟩
   simp_rw [show ∀ p, R p x=(Lr d p y).val from fun p=> reading_at E H p d y]
   exact continuous_subtype_val.comp ((diff_frame E H d y).continuous.comp wire_c)
lemma space_route {p:RealSpin}{s:EuPin}{h:Lorentz.spatialTurn s.coord}(hp:p.coord=Lorentz.room s.coord h)(he:p.matrix=s.matrix) : R p= F.action s := by
   ext x; obtain ⟨d,hx⟩:= E.exhaustive x; let v:Wd F d:=⟨x,hx⟩
   change R p v.val=F.action s v.val; rw [reading_at,levelAct,spatialP_print hp.symm he.symm,prepares]
lemma differentiation (i:SpaceAxis) (v:F.W): HasDerivAt (fun t : ℝ=> R (point (Ray.fromAxis i) t) v)
      ((-Complex.I) • F.lie (Ortho.plane timev i.castSucc) v) 0:=by
   obtain ⟨d,hv⟩:=E.exhaustive v; let x:Wd F d := ⟨v,hv⟩; let L:=Ortho.plane timev i.castSucc; let e:=Ray.fromAxis i
   let u(z:ℂ):=(F.level d).subtypeL (script E H d (Lift.drum e z) x)
   have h : Differentiable ℂ u:= (F.level d).subtypeL.differentiable.comp ((diff_frame E H d x).comp (Lift.drum_diff _))
   let U:= deriv u 0
   have ht : HasDerivAt (fun t:ℝ=> u ((t:ℂ)*I)) (I • U) 0 :=by
       have hi : HasDerivAt (fun t:ℝ => (t:ℂ)*I) I (0:ℝ):= by simpa using! ((Complex.ofRealCLM.hasDerivAt (x:=0)).mul_const I)
       exact (h 0).hasDerivAt.scomp_of_eq (0:ℝ) hi (by simp)
   have hh : HasDerivAt (fun t:ℝ=>u (↑t:ℂ)) U 0:=by
       simpa using! ((h 0).hasDerivAt.scomp_of_eq (0:ℝ) (Complex.ofRealCLM.hasDerivAt (x:=0)) (by simp))
   have ht' (t:ℝ) : u ((t:ℂ)*I)= F.action (Lift.daylight i t) v:=by
       change (script E H d _ x).val=_; rw [Lift.drum_day,prepares]
   have hr : HasDerivAt (fun t:ℝ=> R (point (Ray.fromAxis i) t) v) U 0:= by
       rw [funext (show ∀ t:ℝ, R (point (Ray.fromAxis i) t) v = u t from fun t=> by rw [reading_at E H _ d x]; unfold u levelAct; rw [Lift.drum_real]; rfl)]; exact hh
   simp_rw [ht'] at ht
   rw [← ht.unique (E.infinitesimal _ v _ (Lift.way i)), smul_smul, neg_mul, I_mul_I,neg_neg,one_smul]; exact hr
omit E in
lemma adj_keep {d:ℕ} (v:Wd F d): F.adj timev v.val ∈ F.level d :=by
   obtain ⟨x,rfl⟩:= covering (B:=B) d v
   change F.adj timev (B.choice 0 x) ∈ _
   rw [← H.reality]; exact (B.frame 0 d _).property
lemma adj_rel {p p':EuPin} (h: ∀ d y, UV.adj timev (UV.pinAct (d:=d) p y)=UV.pinAct p' (UV.adj timev y))(x:F.W) : -- p declarations
    F.adj timev (F.action p x)= F.action p' (F.adj timev x):=by
   obtain ⟨d,hd⟩:= E.exhaustive x; obtain ⟨y,hy⟩:= covering (B:=B) d (⟨x,hd⟩ : Wd F d)
   have he:P.sym.adj d timev (P.sym.pin d p y)=P.sym.pin d p' (P.sym.adj d timev y):=Subtype.ext (by simp only [RawSym.adjActs,RawSym.pinActs,h])
   have hy : x=B.choice 0 y:= congr_arg Subtype.val hy |>.symm
   rw [hy,← H.equivariant,← H.reality,← H.reality,← H.equivariant,he]
private def adjV (d:ℕ) : Wd F d →ₛₗ[starRingEnd ℂ] Wd F d where
   toFun x:=⟨F.adj timev x.val,adj_keep H x⟩
   map_add' _ _:= Subtype.ext (map_add (F.adj timev) _ _)
   map_smul' _ _:= Subtype.ext (map_smulₛₗ (F.adj timev) _ _)

lemma boost_star (v:F.W) (i: SpaceAxis) (t:ℝ) : F.adj timev (R (point (Ray.fromAxis i) t) v)= R (point (Ray.fromAxis i) t) (F.adj timev v):=by
   obtain ⟨d,hd⟩:= E.exhaustive v
   haveI:= E.finite d
   let A:= adjV H d; let x:Wd F d:=⟨v,hd⟩; let e := Ray.fromAxis i
   change F.adj timev (R _ x.val)=R _ (A x).val
   rw [reading_at,reading_at]
   apply congr_arg Subtype.val (show A _=(Lr d (point e t)) (A x) from ?_)
   let L(z:ℂ):= script E H d (Lift.drum e z)
   let b:=Module.finBasis ℂ (Wd F d)
   apply b.equivFun.injective; funext j
   let K:=b.coord j
   let N : Module.Dual ℂ (Wd F d):=
      { toFun p := star (K (A p)), map_add' p q:=by rw [map_add,map_add,star_add]
        map_smul' c p :=by rw [map_smulₛₗ,map_smul]; simp }
   let f(z:ℂ):= L z x; let g(z:ℂ):= L z (A x); let u(q:ℂ):= N (f q)
   let w(q:ℂ):= star (u (star q))
   have hf: Differentiable ℂ f:=(diff_frame E H _ _).comp (Lift.drum_diff _)
   have hu: Differentiable ℂ u:=N.toContinuousLinearMap.differentiable.comp hf
   have hg: Differentiable ℂ g:=(diff_frame E H _ _).comp (Lift.drum_diff _)
   have hw: Differentiable ℂ w:= fun p=>differentiableAt_conj_conj_iff.mpr (hu _)
   have hM(z:ℂ) : w z= K (g z):=congr_fun (from_imag_parameter hw (K.toContinuousLinearMap.differentiable.comp hg) (fun s => by
      change star (star (K (A (f _))))=K _; rw [star_star, star_mul]
      apply congr_arg K; apply Subtype.ext
      change F.adj timev ((script E H d (Lift.drum e _) x).val)=(script E H d (Lift.drum e _) _).val
      rw [show star I * star (s:ℂ)= (↑(-s):ℂ)*I by simp [mul_comm],Lift.drum_day, Lift.drum_day, prepares,prepares]
      exact adj_rel E H (fun d y=> by convert Lift.star_day i (-s) y using 1; rw [neg_neg]) x.val)) z
   have he:= hM (t:ℂ); change star (star (K (A (L _ x))))=K (L _ (A x)) at he
   rw [star_star, show star (↑t:ℂ)=(t:ℂ) by simp] at he; unfold L at he; rw [Lift.drum_real] at he; exact he
lemma respects (v:F.W) (p:RealSpin) : F.adj timev (R p v)=R p (F.adj timev v):=by
   have he:= reaches p; induction he using Subgroup.closure_induction generalizing v with
   | mem g hg=>
     rcases hg with ⟨q,h,hp,ht⟩|⟨i,t,rfl⟩
     · rw [space_route E H hp.symm ht.symm]; exact adj_rel E H (fun d _=> Lift.star_spatial q h _) v
     exact boost_star ..
   | one => simp
   | mul x y hx hy ha hb=>rw [map_mul]; simp only [LinearEquiv.mul_apply,ha,hb]
   | inv x hx Hx=> apply (R x).injective; rw [← Hx]; simp
lemma signs (q:RealSpin)(h:q.coord=1)(he:q.matrix= -1) : R q=F.parity:=by
   obtain ⟨p,hp,hc⟩:= SpinGeometry.geometry.euBoth (1:EuPin)
   change 1=p.coord at hp; change p.matrix= -1 at hc
   have hs : Lorentz.spatialTurn p.coord:=by
      rw [←hp]; refine ⟨?_,by simp⟩
      unfold Lorentz.properTurn
      rw [show (Ortho.motion 1).toLinearEquiv.toLinearMap=(LinearMap.id : Module.End ℝ E4) from LinearMap.ext fun x => Ortho.move_one x]
      simp
   calc
     _ = F.action p := space_route E H (h.trans (show 1=Lorentz.room p.coord hs from Lorentz.ext _ _ (fun x=>by
           change Lorentz.act 1 x= Ortho.move p.coord x; rw [←hp]; simp))) (he.trans hc.symm)
     _ = _ := E.sign p hp.symm hc
lemma degrees (q:RealSpin) (x:F.W): R q (F.parity x)=F.parity (R q x):=by
   obtain ⟨p,hp,hc⟩:= SpinGeometry.geometry.minkBoth (1:RealSpin); change 1=p.coord at hp; change p.matrix= -1 at hc
   have hh: p*q=q*p:=by
       apply Subtype.ext; apply Prod.ext
       · change p.coord*q.coord=q.coord*p.coord; rw [←hp]; simp
       apply Units.ext; change p.matrix.val*q.matrix.val=q.matrix.val*p.matrix.val; rw [hc]; simp
   rw [← signs E H p hp.symm hc, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul, hh]
lemma all : Nonempty (WSpins F):=by
   refine ⟨R, fun d p x h=>life E H p d x h, continuous_route E H, fun p h q H' e=>space_route E H H' e,?_,fun q v=>(respects E H v q).symm,degrees E H, signs E H,?_⟩
   · intro i p hp x; rw [Lift.prescribed i p hp]; exact differentiation E H i _
   intro r d x; exact ⟨fun z=>script E H d (Lift.drum r z) x,(diff_frame E H d x).comp (Lift.drum_diff _),fun t=> by dsimp only; rw [Lift.drum_real]; exact (reading_at E H _ _ x).symm⟩
#print axioms all
end Spinor
end YM.Massive.Bridge
