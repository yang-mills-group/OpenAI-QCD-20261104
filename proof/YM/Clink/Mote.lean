import YM.Clink.Pale
import YM.Pollen.Road
/-! Point product inserted hops represented as bloom single series. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.QCD.Entr.Meridian
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator Kronecker
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ C C' α α' ξ:ℝ}{i o: Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden
open WardBin.Lies Eyrie Rudder Massive.PCAC
open Metric
variable (o x:Site c)(W:Bloom k)(i j:Walk)(s:Step)(V:Grid c)
noncomputable def punct (o:Site c): Sheet c:=rides (Equiv.refl _) fun p=>if p=o then 1 else 0
local notation "D"=>punct o
lemma ζD (p q:Lat.Row c): (D) p q= if p.1=o then (1:Sheet c) p q else 0:=by unfold punct; rw [rr]; simp only[Equiv.refl_apply]; rcases p with ⟨p,i⟩; rcases q with ⟨q,j⟩; split_ifs <;> simp_all [Matrix.one_apply]
lemma cashD (N:ℕ) : copies N (D)= Massive.PCAC.zone N o:=by
     ext i j; unfold copies; rcases i with ⟨i,a⟩; rcases j with ⟨j,b⟩; simp only[Matrix.blockDiagonal_apply,ζD]; by_cases h:i=j <;> split_ifs <;> simp_all [Massive.PCAC.zone,Matrix.one_apply,Matrix.diagonal_apply] -- disamb locale
local notation "R" i:arg=> routeM 0 V i
local notation "L"=> leg 0 V s
local notation "w" i:arg=> Equiv.addRight (wrap c (stop (0:Cover) i))
local notation "A" x:arg=> trackP W ξ c V x -- not arg
lemma reefer : routeM (0: Site c) V [s]=leg 0 V s:=by unfold routeM; rw[List.map_singleton,List.prod_singleton]
lemma snowV(b: Site c)(Q:Walk) : (w Q) b = stop b Q:= (wrap_stop b Q).symm
lemma glint_k (p:Site c) : winding p (i++j) 0 V=winding p i 0 V* winding (stop p i) j 0 V:=by
      unfold winding; rw [travel_append,Revolve.shone,Matrix.smul_mul,Matrix.mul_smul, touch_mul, ← colour_mul, smul_smul, mul_comm (shimmer 0 _ _)]; -- check
variable (ξ:ℝ)
local notation "U"=>trackP W ξ c V
local notation "G"=> W.tail
 -- pre-anchor by tail
lemma kef (h:stop x G=o): let K:= episode W ([]:Walk) (G++[s]) x ξ; (U)*(D*L)= blockL x (stop x (G++[s])) (K (settled V)):=by
       intro K
       rw [trackP,←reefer]; unfold punct LeafM.yard; rw [pinned V 0 G,pinned V 0 [s],ride_mul,ride_mul,ride_mul]; ext ⟨p,i'⟩ ⟨q,j'⟩; rw [rr]; have ht : Equiv.trans (Equiv.trans (Equiv.refl (Site c)) ((w G))) ((Equiv.refl (Site c)).trans ((w [s]))) p=stop p (G++ [s]):=by simp only [Equiv.trans_apply,Equiv.refl_apply,snowV,stop_append]
       change (if _ then (((satin W p ξ V)*(winding ((Equiv.refl _) p) G 0 V))* (_*_)) i' j' else 0)= if p=x ∧ q= stop x (G++[s]) then K (settled V) i' j' else 0
       simp only [Equiv.trans_apply,Equiv.refl_apply,snowV] at *
       by_cases hu:p=x; swap
       · have hh:stop p G≠o:=by rw[←h,← snowV,←snowV]; exact (((w G))).injective.ne hu
         rw [if_neg (show ¬ (p=x∧ _) from (fun hh=>hu hh.1))]; split; next h=> rw[zero_mul,mul_zero]; rfl
         next _=> rfl
       subst p; split; next hx=>
            have hh : q=stop x (G++[s]):= hx.symm.trans ht -- ht if simpl rw maybe ht now
            rw [if_pos ⟨rfl,hh⟩,one_mul]; unfold K episode; simp only [Pi.mul_apply,woS,stop,satin_eq]; rw[show winding x [] 0 V=1 from (by simp[winding,Lattice.travel,shimmer,show Lat.colour (1:su.El)=1 from rfl,touch_one]),one_mul,glint_k, Matrix.mul_assoc]
       next hx=> rw[if_neg (fun h=>hx (?_))]; exact (h.2 ▸ ht) -- edit
lemma kreb (h:stop x [s]=o) : U= U:=rfl -- temp
lemma berg (h:stop x [s]=o): let K:=episode W [s] G x ξ; (L*D)*U=blockL x (stop o G) (K (settled V)):=by
       intro K; rw[trackP,←reefer]; unfold punct LeafM.yard; rw[pinned V 0 G,pinned V 0 [s],ride_mul,ride_mul,ride_mul]; ext ⟨p,i'⟩ ⟨q,j'⟩; rw [rr]; change _= if p=x∧ q=stop o G then K (settled V) i' j' else 0; simp only[Equiv.trans_apply,Equiv.refl_apply,snowV]; by_cases he :p=x
       swap
       · have hh:stop p [s]≠o:=by rw[←h,← snowV,←snowV]; exact (((w [s]))).injective.ne he
         rw [if_neg (show ¬ (p=x∧ _) from fun hh=>he hh.1)]; split; next h=> rw[mul_zero,zero_mul]; rfl
         next _=>rfl
       subst p; change _=_; split
       next hp=>
            rw [if_pos ⟨rfl,(hp.symm.trans (by rw[h]))⟩,mul_one]; unfold K episode; simp only [Pi.mul_apply,woS,satin_eq]; rw [mul_assoc]
       next hp=> rw[if_neg (fun h'=> hp (((congr_arg (fun y=>stop y G) h).trans h'.2.symm)))]
end YM.QCD.Entr.Meridian
#print axioms YM.QCD.Entr.Meridian.kef
#print axioms YM.QCD.Entr.Meridian.berg
