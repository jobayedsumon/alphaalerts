
import fetchWrapper from "./fetchWrapper";
import jwtDecode from "jwt-decode";
import {swalError, swalSuccess} from "./common";

export const login = (email, password) => {
    fetchWrapper.post('/api/login', {
        email: email,
        password: password
    }).then((response) => {
        const data = response.data;
        if (data.status === 'success' && data.token && data.user) {
            localStorage.setItem('token', data.token);
            localStorage.setItem('user', JSON.stringify(data.user));
            fetchWrapper.defaults.headers.common['Authorization'] = 'Bearer ' + data.token;
            swalSuccess('Login successful');
            window.location.href = '/';
        } else {
            swalError("Invalid email or password");
        }
    }).catch((error) => {
        swalError("Error logging in");
    });
}

export const isLoggedIn = () => {
    const user = JSON.parse(localStorage.getItem('user'));
    const token = localStorage.getItem('token');
    if (user && token) {
        const decodedToken = jwtDecode(token);
        const currentTime = Date.now() / 1000;
        return decodedToken.exp >= currentTime;
    } else {
        return false;
    }
}

export const logout = () => {
    localStorage.removeItem('token');
    localStorage.removeItem('user');
    delete fetchWrapper.defaults.headers.common['Authorization'];
    window.location.href = '/';
}
