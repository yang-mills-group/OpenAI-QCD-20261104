import YM.Arise.Gam
import YM.Arise.Per
import YM.Arise.Star
import YM.Vest.Key
import YM.Play.Panther
import YM.Profiles.Quills
/-! # Tilt-graded truth under article stakes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Bill
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical TensorProduct
open Massive UV UV.Free QCD QCD.Grass QCD.Bera QCD.Cove QCD.Anomaly QCD.Creek Count Vest
open MassiveQCD.Sample.Quills
open MassiveQCD.Ribbon
open YM.Arise.Range
variable {A I U X Y:Type}[Fintype A][Fintype I][Fintype U][Fintype X][Fintype Y]
variable {n m j k d:ℕ}
noncomputable def Grace (d:ℕ)(b:Bool):Submodule ℂ (SpinPol d) where
    carrier:={x| Hom b x}
    zero_mem':= Hom.zero _
    add_mem' :=fun hx hy=> Hom.add hx hy
    smul_mem' :=fun i x h=> Hom.smul h i
noncomputable abbrev Cups(d:ℕ)(b:Bool):= Lily su d ⊗[ℂ] ↥(Grace d b)
section
open TensorProduct
noncomputable def meaning(d:ℕ)(b:Bool): Cups d b→ₗ[ℂ] UV.Pol d:= TensorProduct.map (rollK _ _).toLinearMap (Grace d b).subtype
end
variable (q:I→Bool)(w:I→ℕ) (x:I→E4)(f:Fin n→I)
abbrev Svg (w:I→ℕ):= ClockG su w
abbrev Tv (w:I→ℕ):= Arms w ⊕ Spine I
local notation "Cv"=> Arms w
local notation "Si"=> Spine I
local notation "Ct"=> Tv w
local notation "Uu"=> U ⊕ Spine I
noncomputable def house (i:I):Grace (w i) (q i) →ₗ[ℂ] Patio (Tv w):= ((MassiveQCD.Ribbon.stake Cv (MassiveQCD.Ribbon.burst q {i})).toLinearMap ∘ₗ ((ham I i w).toLinearMap ∘ₗ (Grace _ _).subtype)).codRestrict (roomA (Tv w)).toSubmodule fun u=> by
    let A:=u.val; apply even_stake _ _; have hp: Hom (q i) A:=u.property; rw [MassiveQCD.Ribbon.flavor]; change Hom (q i) (ham I i w A); unfold ham; cases ht:q i <;> rw [ht] at hp
    · exact (embed_grade ..).trans (congr_arg _ hp)
    exact (embed_grade ..).trans ((congr_arg (embed (fun x:Pairs (SpinMode (w i))=>(⟨i,x⟩:Arms w))) (show grade A= -A from hp)).trans (map_neg _ _))
noncomputable def nameG (i:I): Lily su (w i) →ₐ[ℂ] MvPolynomial (Svg w) ℂ:= MvPolynomial.rename fun y=> (⟨i,y⟩:Svg w)
local notation "Ψs"=> Papers (Svg w) (Patio Ct)
noncomputable def port (i:I): Cups (w i) (q i)→ₗ[ℂ] Papers (Svg w) (Patio Ct):=TensorProduct.lift
    ({ toFun:= fun P=> (Bera.outer (nameG w i P)).comp (house q w i)
       map_add' x y:= by apply LinearMap.ext; intro p; change outer (nameG w i (x+y)) (house q w i p)=outer (nameG w i x) (house q w i p)+outer (nameG w i y) (house q w i p); rw [map_add,outadd]
       map_smul' r x:= by apply LinearMap.ext; intro p; change outer (nameG w i (r • x)) (house q w i p)=r • outer (nameG w i x) (house q w i p); rw [map_smul,outs] } : Lily su (w i) →ₗ[ℂ] _ →ₗ[ℂ] _)
lemma portal (i:I)(p:Lily su (w i))(u: Grace (w i) (q i)): port q w i (p ⊗ₜ[ℂ]u) = outer (nameG w i p) (house q w i u):= TensorProduct.lift.tmul ..
local notation "Ub"=> Papers Unit (Patio Uu)
noncomputable def stampU (U:Type)[Fintype U] (w:I→ℕ)(x:I→E4) : Tone (Svg w) (Tv w) Unit (U⊕Spine I):= ⟨0,call x w,breezeP (Spine I) (0:Matrix (Arms w) U ℂ),breezeX (Spine I) (callS x w)⟩
-- Want needle eq directly on Alg Uu
local notation "Θm"=> stampU U w x
local notation "Oh"=> Oce.rose Uu
section Polar
open MassiveQCD.Ribbon
open MvPolynomial Next.Rank.Normal
-- all evaluations. define Real val.U
noncomputable def taxer (A B:Type)[Fintype A][Fintype B](x:A→ℝ): Papers A (Patio B)→ₗ[ℂ] Patio B:= (Oce.rose B x).toLinearMap.restrictScalars ℂ
lemma turned (p:poly (Svg w))(v:Patio Ct): (Oh (fun _:Unit=>1) ((Θm).read (outer p v))).val=(blend (call x w) 0 p) • MassiveQCD.Ribbon.carry Si ((Pair.offP Cv U).toLinearMap.toContinuousLinearMap.comp (Creek.birth (Wand (callS x w)))) v.val:=by
    rw [Tone.spree,Oce.antiquity]
    let V:=(call (G:=su) x w); let H:=fun _:Unit=>(1:ℝ); have hp : Oce.eve H (Next.Rank.Normal.pipe (spool (Θm).P) V p)=blend V 0 p:=by
         unfold pipe; rw [LinearMap.comp_apply]; change aeval _ (exchange _ (milk _ _))=blend _ _ _; rw [reads_val, show (reads (spool (Θm).P) (fun y:Unit=> (H y:ℂ)))=0 from funext fun i=> by
               unfold reads; have hz: spool (Θm).P i=0:=Finsupp.ext fun j=>Tone.spi (Θm).P i j; rw [hz,map_zero]; rfl]; rfl
    change (Oce.eve H ((pipe (spool (Θm).P) V) p)) • (splash (stampU U w x).M (stampU U w x).V v).val= _; rw [hp]; exact congr_arg (fun x=> blend V 0 p • x) (rimy Si (callS x w) (0:Matrix Cv U ℂ) v) -- ambiguity
end Polar
section Prod
variable (g:(i:Fin n)→Lily su (w (f i)))(v:(i:Fin n)→ Grace (w (f i)) (q (f i)))

lemma pars : (List.ofFn (fun i:Fin n=> port q w (f i) (g i⊗ₜ[ℂ]v i))).prod= outer (∏ i,nameG w (f i) (g i)) (List.ofFn (fun i:Fin n=>house q w (f i) (v i))).prod:=by
    induction n with
    | zero=> simp [outP]
    | succ n ih=>
       let F(i:Fin n):=f i.succ; let V(i:Fin n):=v i.succ; let G(i:Fin n):=g i.succ; let P(i:Fin n):= nameG w (F i) (G i); let H(i:Fin n):=house q w (F i) (V i)
       have he:= ih F G V; rw [List.ofFn_succ,List.prod_cons, Fin.prod_univ_succ]; change port q w _ (g 0⊗ₜ[ℂ] v 0)* _=_; rw [portal]; erw [he]; rw [outMul]; congr 2; rw [List.ofFn_succ,List.prod_cons]
lemma wells : (List.ofFn (fun i:Fin n=> house q w (f i) (v i))).prod.val = MassiveQCD.Ribbon.fiber (Spine I) (List.ofFn (fun i:Fin n=>ham I (f i) w (v i).val)).prod * MassiveQCD.Ribbon.quill Cv (armature q f):=by
    induction n with
    | zero=> let B:Alg (Arms w⊕ Spine I):= 1; simp [armature] -- maybe
    | succ n ih=>
       let a:= f 0; let F(i:Fin n):=f i.succ; let V(i:Fin n):=v i.succ; let U:=(List.ofFn (fun i:Fin n=> house q w _ (V i))).prod; let y:=U.val
       let W:= (List.ofFn (fun i:Fin n=>ham I (F i) w (V i).val)).prod; let C:= (fiber (Spine I) (A:=Arms w)); let S:=quill (Arms w) (B:=Spine I); let G:=ham I a w (v 0).val
       have ht:y=C W*S (armature q F):=ih _ V; let X:=S (mono (MassiveQCD.Ribbon.burst q {a})); have he: Plus y:=U.property
       conv_lhs=> rw [List.ofFn_succ,List.prod_cons]
       conv_rhs=> rw [arm, List.ofFn_succ (f:=fun i:Fin (n+1)=>ham I (f i) w (v i).val), List.prod_cons,map_mul,map_mul]
       change C G * X * y = C G*C W*(S (armature q F)*X); rw [mul_assoc,(he.central X).eq,ht]; simp only [mul_assoc]
lemma feesW (hx:points (x∘f)∈ conf n) :
    (Oh (fun _:Unit=>1) (Tone.read Θm (List.ofFn (fun i:Fin n=> port q w (f i) (g i⊗ₜ[ℂ]v i))).prod)).val = fiber Si (UV.Free.moment (w∘f) (points (x∘f)) (fun i=>meaning _ _ (g i ⊗ₜ[ℂ] v i)) • (1:Alg U))* quill U (armature q f):=by
    rw [pars,turned,wells,carries_r]; let h(i:Fin n):= f i; let Z:=(List.ofFn (fun i:Fin n=>ham I (f i) w (v i).val)).prod
    let L:=(Pair.offP Cv U).toLinearMap.toContinuousLinearMap.comp (Creek.birth (Wand (callS x w))); have hq: MassiveQCD.Ribbon.carry Si L (fiber Si Z)=fiber Si (erg I x w Z):=by rw [←MassiveQCD.Ribbon.quiet,MassiveQCD.Ribbon.speaks,MassiveQCD.Ribbon.quiet]; rfl
    rw [hq,← _root_.smul_mul_assoc, ← map_smul]; congr 2 -- equality inside fiber
    rw [show Next.Rank.Normal.blend (call x w) 0 (∏ i:Fin n,nameG w _ (g i))=_ from (highlight f x hx w g).symm]; have hv (i:Fin n): meaning _ _ (g i⊗ₜ[ℂ] v i)=(rollK _ _ (g i))⊗ₜ[ℂ] (v i).val:=TensorProduct.map_tmul ..; erw [funext hv]; exact gammaCost I f w x hx _ _
end Prod
end YM.Arise.Bill
#print axioms YM.Arise.Bill.feesW
