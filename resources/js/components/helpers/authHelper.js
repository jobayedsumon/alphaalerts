import fetchWrapper from "./fetchWrapper";
import jwtDecode from "jwt-decode";
import {swalError, swalSuccess} from "./common";
import {useDispatch, useSelector} from "react-redux";

export const login = (email, password) => {
    return fetchWrapper.post('/api/login', {
        email: email,
        password: password
    }).then((response) => {
        const data = response.data;
        if (data.status === 'success' && data.token && data.user) {
            return data;
        } else {
             swalError("Invalid email or password");
        }
    }).catch((error) => {
         swalError("Error logging in");
    });
}

export const walletConnect = async (e) => {
        if (!window.ethereum) {
             swalError("No crypto wallet found. Please install it.");
        }
        return window.ethereum.request({method: 'eth_requestAccounts'})
            .then(res => {
                const address = res[0];
                return fetchWrapper.post('/api/wallet-connect', {
                    wallet_address: address
                }).then((response) => {
                        const data = response.data;
                        if (data.status === 'success' && data.token && data.user) {
                            return data;
                        } else {
                             swalError("Invalid wallet address");
                        }
                    }
                ).catch((error) => {
                         swalError("Error connecting wallet");
                    }
                );
            })

}

export const isLoggedIn = () => {
    const user = useSelector(state => state.user);
    const token = useSelector(state => state.token);
    if (user && token) {
        const decodedToken = jwtDecode(token);
        const currentTime = Date.now() / 1000;
        return decodedToken.exp >= currentTime;
    } else {
        return false;
    }
}

export const isAdmin = () => {
    const user = useSelector(state => state.user);
    return user && user.is_admin === 1;
}

export const logout = () => {
    delete fetchWrapper.defaults.headers.common['Authorization'];
    window.location.href = '/';
}
