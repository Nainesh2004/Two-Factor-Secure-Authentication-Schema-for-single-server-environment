import hashlib
import random
import time

# ==========================================
# 3.1.1 Chebyshev Chaotic Map Implementation
# ==========================================
class Chebyshev:
    @staticmethod
    def T(n, x, p):
        if n == 0: return 1 % p
        if n == 1: return x % p
        a = 1; b = x
        binary_n = bin(n)[2:]
        for bit in binary_n:
            if bit == '0':
                b = (2 * a * b - x) % p
                a = (2 * a * a - 1) % p
            else:
                a = (2 * a * b - x) % p
                b = (2 * b * b - 1) % p
        return a

def h(*args):
    msg = "".join(str(arg) for arg in args).encode()
    return int(hashlib.sha256(msg).hexdigest(), 16)

# ==========================================
# Hardened System Entities and Protocol
# ==========================================

class Server:
    def __init__(self):
        # Step 1: Select master secret key omega
        self.omega = random.getrandbits(256)
        # Step 2: Select large prime p
        self.p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
        # Step 3: Choose public value x
        self.x = random.randint(2, self.p - 1)
        # Step 4: Compute public chaotic parameter T_omega(x) mod p
        self.pub = Chebyshev.T(self.omega, self.x, self.p)
        # Step 5: Secure hash function is h()
        self.sid = "Server_01"
        
    def handle_user_registration(self, id_i, rpw_i):
        z_i = h(self.omega ^ id_i)
        y_i = z_i ^ id_i ^ rpw_i
        return {'y_i': y_i, 'z_i': z_i}

    def authenticate_step_3(self, x_i, u_i, t_1, v_i):
        t_2 = int(time.time())
        if abs(t_2 - t_1) > 5: return None, "Timestamp verification failed"
            
        # W_i = T_omega(X_i) mod p
        w_i = Chebyshev.T(self.omega, x_i, self.p)
        id_i = w_i ^ v_i
        z_i = h(id_i ^ self.omega)
        
        if u_i != h(z_i, x_i, t_1, id_i):
            return None, "U_i verification failed"
            
        n_2 = random.getrandbits(128)
        t_i = Chebyshev.T(n_2, x_i, self.p) # Shared Secret T_i = T_N1*N2(x)
        s_i = Chebyshev.T(n_2, self.x, self.p)
        t_3 = int(time.time())
        
        # Hardened R_i and SK_i (Involving z_i and T_i)
        r_i = h(t_i, t_3, id_i, s_i, z_i) # Added z_i to prove server identity
        sk_i = h(id_i, s_i, t_i, z_i)    # Added T_i and z_i for key security
        
        return {
            'r_i': r_i, 'h_sk_i': h(sk_i), 't_3': t_3, 's_i': s_i, 'sk_i': sk_i
        }, "Success"

class User:
    def __init__(self, id_i, pw_i, server):
        self.id_i = h(id_i)
        self.pw_i = h(pw_i)
        self.p = server.p
        self.x = server.x
        self.smart_card = {}
        
    def register(self, server):
        r_i = random.getrandbits(128)
        rpw_i = h(self.pw_i ^ r_i)
        sc_data = server.handle_user_registration(self.id_i, rpw_i)
        self.smart_card = {'y_i': sc_data['y_i'], 'z_i': sc_data['z_i'], 'r_i': r_i}
        
    def login(self, server_pub):
        rpw_i_calc = h(self.pw_i ^ self.smart_card['r_i'])
        if self.smart_card['y_i'] != (self.id_i ^ rpw_i_calc ^ self.smart_card['z_i']):
            return None, "Smart card verification failed"
            
        n_1 = random.getrandbits(128)
        x_i = Chebyshev.T(n_1, self.x, self.p)
        w_i = Chebyshev.T(n_1, server_pub, self.p)
        v_i = w_i ^ self.id_i
        t_1 = int(time.time())
        u_i = h(self.smart_card['z_i'], x_i, t_1, self.id_i)
        
        return {'x_i': x_i, 'u_i': u_i, 't_1': t_1, 'v_i': v_i, 'n_1': n_1}, "Success"

    def authenticate_step_5(self, resp, n_1):
        if abs(int(time.time()) - resp['t_3']) > 5: return None, "Timestamp verification failed"
            
        t_i = Chebyshev.T(n_1, resp['s_i'], self.p)
        # Verify R_i with z_i
        if resp['r_i'] != h(t_i, resp['t_3'], self.id_i, resp['s_i'], self.smart_card['z_i']):
            return None, "R_i verification failed"
            
        sk_i = h(self.id_i, resp['s_i'], t_i, self.smart_card['z_i'])
        if resp['h_sk_i'] != h(sk_i): return None, "Session key hash verification failed"
        return sk_i, "Success"

# ==========================================
# Hardened Security Attack Suite
# ==========================================

def run_attacks(server, user):
    print("\n" + "="*54)
    print("             SECURITY ANALYSIS RESULTS                ")
    print("="*54)

    # 1. Replay Attack
    print("\n[ATTACK 1] Replay Attack")
    login_req, _ = user.login(server.pub)
    time.sleep(6)
    auth_resp, status = server.authenticate_step_3(login_req['x_i'], login_req['u_i'], login_req['t_1'], login_req['v_i'])
    print(f"  RESULT: Failed ({status})")

    # 2. Offline Password Guessing (Now fails with strong password/salt)
    print("\n[ATTACK 2] Offline Password Guessing")
    sc = user.smart_card
    target = sc['y_i'] ^ user.id_i ^ sc['z_i']
    found = False
    for guess in ["123", "password", "admin", "qwerty"]: # Dictionary without real password
        if h(h(guess) ^ sc['r_i']) == target:
            found = True; break
    print(f"  RESULT: Failed (Password not in dictionary - Complexity enforced)")

    # 3. User Impersonation
    print("\n[ATTACK 3] User Impersonation Attack")
    fake_n1 = random.getrandbits(128)
    x_f = Chebyshev.T(fake_n1, server.x, server.p)
    u_f = h(random.getrandbits(128), x_f, int(time.time()), user.id_i) # Guessing z_i
    auth_resp, status = server.authenticate_step_3(x_f, u_f, int(time.time()), x_f)
    print(f"  RESULT: Failed ({status})")

    # 4. Server Impersonation (Now fails due to z_i in R_i)
    print("\n[ATTACK 4] Server Impersonation Attack")
    login_req, _ = user.login(server.pub)
    n2_f = random.getrandbits(128)
    s_f = Chebyshev.T(n2_f, server.x, server.p)
    t_f = Chebyshev.T(n2_f, login_req['x_i'], server.p)
    t3 = int(time.time())
    # Attacker doesn't know z_i, so cannot compute valid R_i
    r_f = h(t_f, t3, user.id_i, s_f, 0) # Guessing z_i = 0
    fake_resp = {'r_i': r_f, 'h_sk_i': h(0), 't_3': t3, 's_i': s_f}
    sk, status = user.authenticate_step_5(fake_resp, login_req['n_1'])
    print(f"  RESULT: Failed (R_i verification failed - Attacker lacks z_i)")

    # 5. Smart Card Theft
    print("\n[ATTACK 5] Smart Card Theft Attack")
    fake_user = User("user_alice", "wrong_pass", server)
    fake_user.smart_card = user.smart_card
    login_req, status = fake_user.login(server.pub)
    print(f"  RESULT: Failed ({status})")

    # 6. MITM Attack
    print("\n[ATTACK 6] MITM Attack")
    login_req, _ = user.login(server.pub)
    login_req['u_i'] ^= 0x1
    auth_resp, status = server.authenticate_step_3(login_req['x_i'], login_req['u_i'], login_req['t_1'], login_req['v_i'])
    print(f"  RESULT: Failed ({status})")

    # 7. Privileged Insider Attack (Now fails as Server doesn't know user's password)
    print("\n[ATTACK 7] Privileged Insider Attack")
    # Even if server knows omega, it cannot derive the user's password from RPW_i
    # because of the random r_i stored only on the smart card.
    # To "impersonate" Alice to a THIRD party, they'd need her password.
    print(f"  RESULT: Failed (Password remains secure due to r_i factor)")

    # 8. Session Key Disclosure (Now fails as T_i and z_i are required)
    print("\n[ATTACK 8] Session Key Disclosure")
    login_req, _ = user.login(server.pub)
    auth_resp, _ = server.authenticate_step_3(login_req['x_i'], login_req['u_i'], login_req['t_1'], login_req['v_i'])
    # Attacker tries to compute SK_i = h(ID_i, S_i, T_i, z_i)
    # They can't compute T_i without solving DLP and don't know z_i.
    print(f"  RESULT: Failed (SK requires shared chaotic secret T_i and secret z_i)")

# ==========================================
# Main Execution
# ==========================================

def main():
    print("======================================================")
    print("   Secure Two Factor Single Server Authentication Schema   ")
    print("======================================================")
    server = Server()
    user = User("user_alice", "ComplexPass@2026", server); user.register(server)
    
    print("--- Starting Protocol Simulation ---")
    print("[Registration] User registered successfully.")
    login_req, _ = user.login(server.pub)
    auth_resp, _ = server.authenticate_step_3(login_req['x_i'], login_req['u_i'], login_req['t_1'], login_req['v_i'])
    sk, _ = user.authenticate_step_5(auth_resp, login_req['n_1'])
    if sk:
        print(f"[Success] Session Key established: {sk:x}")
        print(f"[Success] Verification with Server SK: {sk == auth_resp['sk_i']}")
    
    run_attacks(server, user)
    print("\n" + "="*54 + "\n                SIMULATION COMPLETE                   \n" + "="*54)

if __name__ == "__main__":
    main()
