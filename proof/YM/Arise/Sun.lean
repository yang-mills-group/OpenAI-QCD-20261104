import YM.Arise.Bill
/-! # Tilt arrival.Full subset and momentum. -/
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
variable (q:I→Bool)(w:I→ℕ) (x:I→E4)(f:Fin n→I)
local notation "Cv"=> Arms w
local notation "Si"=> Spine I
local notation "Ct"=> Tv w
local notation "Uv"=> U ⊕ Spine I
local notation "Θm"=> stampU U w x
local notation "Oh"=> Oce.rose Uv
variable (V: ∀ i: I, Cups (w i) (q i))
local notation "gz"=> ∏ i∈crest f,port q w i (V i)
lemma sparkW (P: (i:Fin n)→ Cups (w (f i)) (q (f i)))(hx:points (x∘f)∈ conf n): (Oh (fun _:Unit=>1) (Tone.read Θm (List.ofFn (fun i:Fin n=> port q w (f i) (P i))).prod)).val=fiber Si (UV.Free.moment (w∘f) (points (x∘f)) (fun i=> meaning _ _ (P i)) • (1:Alg U))*quill U (armature q f):=by
    let Ia (i:Fin n):=Cups (w (f i)) (q (f i)); let V':=(light Uv).toLinearMap ∘ₗ (taxer Unit Uv (fun _=>1)) ∘ₗ (Tone.read Θm); let W:MultilinearMap ℂ Ia (Alg Uv):= V'.compMultilinearMap ((MultilinearMap.mkPiAlgebraFin ℂ n (Papers (Svg w) (Patio Ct))).compLinearMap fun i=> port q w (f i)); let Z: (ℂ→ₗ[ℂ]Alg Uv):= (LinearMap.mulRight ℂ (quill U (armature q f))) ∘ₗ ((fiber Si).toLinearMap ∘ₗ LinearMap.toSpanSingleton ℂ (Alg U) (1:Alg U)); let M:MultilinearMap ℂ Ia (Alg Uv):= Z.compMultilinearMap ((UV.Free.moment (w ∘ f) (points (x∘f))).compLinearMap fun i=>meaning (w (f i)) (q (f i)))
    let A(i: Fin n):= MvPolynomial.basisMonomials (Tube su (w (f i))) ℂ; let B(i:Fin n):=Module.finBasis ℂ (Grace (w (f i)) (q (f i)))
    suffices he:W=M from DFunLike.congr_fun he P
    apply Count.roof W M (fun i=> Module.Basis.tensorProduct (A i) (B i)) -- missing universe
    intro v
    let p' i:=A i (v i).1; let q' i:= B i (v i).2; have he(i:Fin n):Module.Basis.tensorProduct (A i) (B i) (v i)=p' i ⊗ₜ[ℂ] q' i:= Module.Basis.tensorProduct_apply' ..
    let u(i:Fin n):Ia i:=p' i⊗ₜ[ℂ] q' i; change W _=M _; erw [funext he]; change W u=M u; exact feesW q w x f p' q' hx
lemma colored (h:Injective f)(hx:points (x∘f)∈conf n):(Oh (fun _:Unit=>1) ((Θm).read (∏ i∈crest f,port q w i (V i)))).val=fiber Si (UV.Free.moment (w ∘ f) (points (x∘ f)) (fun i=> meaning _ _ (V (f i))) • (1:Alg U))*quill U (armature q f):=by
   rw [show (∏ i∈crest f, port q w i (V i))=(List.ofFn (fun i=>port q w (f i) (V (f i)))).prod from (?_)]; exact sparkW _ _ _ f _ hx; unfold crest; rw [prod_image h.injOn,List.prod_ofFn]
noncomputable def sumW (A:Type)[Fintype A] (X x:ℂ)(q:Alg (Spine I)):= fiber Si (x • (1: Alg A))*quill A q
-- parcel l.O.
noncomputable def pays (X:Finset I): Patio Uv:= Oh (fun _:Unit=>1) ((Θm).read (∏ i∈ X,port q w i (V i)))
lemma pay_f (h:Injective f)(hx:points (x∘ f)∈conf n): MassiveQCD.Sample.Quills.numbered q U f (pays q w x V (crest f))=(UV.Free.moment (w∘f) (points (x∘f)) (fun i=>meaning _ _ (V (f i))) • (1:Alg U)):=MassiveQCD.Sample.Quills.cuts _ _ _ h _ _ (colored q w x f V h hx)
lemma pay_log (h:Injective f)(hx:points (x∘f)∈conf n):∃ a:ℂ,(pays (U:=U) q w x V (crest f)).val=MassiveQCD.Ribbon.stake U (MassiveQCD.Ribbon.burst q (crest f)) (a • (1:Alg U)):=by
    obtain ⟨hn,ht,hs⟩:= arm_bill q f h; let z:=UV.Free.moment (w∘f) (points (x∘f)) (fun i=> meaning _ _ (V (f i))); let c:=signG q f; refine ⟨z*c,?_⟩; rw [MassiveQCD.Ribbon.markedOut,hs]; change (Oh _ _).val= _; change (pays q w x V (crest f)).val= _; unfold pays; rw [colored q w x f V h hx]; rw [map_smul (quill ..),map_smul (fiber Si), map_smul (fiber Si),mul_smul_comm, _root_.smul_mul_assoc, _root_.smul_mul_assoc]; change z • _= c • (z*c) • _; rw [smul_smul,show c*(z*c)=z from by rw [mul_left_comm,ht,mul_one]] -- ht
end YM.Arise.Bill
#print axioms YM.Arise.Bill.pay_log
